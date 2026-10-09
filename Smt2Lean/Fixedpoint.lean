import Smt2Lean.Chc

namespace Smt2Lean.Fixedpoint

/-- A bounded Z3 dialect lowered to scoped Horn safety queries. Source locations
refer to the original commands, including the synthetic assertion at each query. -/
structure Script where
  text : String := ""
  sources : Array Source.Ref := #[]
  skipped : Array Source.Command := #[]

private def Script.add (script : Script) (text : String) (source : Source.Ref) : Script :=
  { script with text := script.text ++ text ++ "\n", sources := script.sources.push source }

/-- Split one list into complete token groups; native cvc5 still parses all terms. -/
private def fields (text : String) : Except String (Array String) := do
  let tokens := Source.tokenize text
  unless tokens[0]? == some "(" && tokens.back? == some ")" do
    throw "expected a parenthesized list"
  let mut result := #[]
  let mut group := #[]
  let mut depth := 0
  for token in tokens.extract 1 (tokens.size - 1) do
    if token == ")" then
      if depth == 0 then throw "unexpected closing parenthesis"
      depth := depth - 1
    group := group.push token
    if token == "(" then depth := depth + 1
    if depth == 0 then
      result := result.push (String.intercalate " " group.toList)
      group := #[]
  unless depth == 0 do throw "unclosed token group"
  return result

private def symbol (text : String) : Except String String := do
  let #[token] := Source.tokenize text | throw "expected one symbol"
  if token.startsWith "|" && token.endsWith "|" then
    return (token.drop 1 |>.dropEnd 1).toString
  unless token.toList.head?.any (fun c => c.isAlpha || "~!@$%^&*_-+=<>.?/".contains c) &&
      !#["true", "false", "let", "forall", "exists", "!", "_", "as"].contains token do
    throw "expected an SMT-LIB identifier"
  return token

private def checkSort (text : String) : Except String Unit := do
  if #["Int", "Bool", "Real"].contains text then return
  if let #["(", "_", "BitVec", width, ")"] := Source.tokenize text then
    if let some n := width.toNat? then
      if n > 0 && width.toList.all Char.isDigit && !width.startsWith "0" then return
  throw "fixedpoint supports Bool, Int, Real and positive-width BitVec sorts"

private structure State where
  script : Script := {}
  relations : Array (String × Array String) := #[]
  variables : Array (String × String) := #[]
  names : Array String := #[]
  queries : Nat := 0
  exited : Bool := false

private def command (state : State) (command : Source.Command) (stem : String)
    : Except String State := do
  if state.exited then throw "unexpected command after exit"
  let args ← fields command.text
  let kind := args[0]?.getD ""
  let script := if state.script.sources.isEmpty then
    state.script.add "(set-logic HORN)" command.source else state.script
  let state := { state with script }
  match kind with
  | "set-logic" =>
    unless args == #["set-logic", "HORN"] || args == #["set-logic", "ALL"] do
      throw "fixedpoint expects HORN or ALL logic"
    return state
  | "set-option" =>
    unless args.size == 3 && args[1]! == ":fp.engine" &&
        #["spacer", "datalog"].contains args[2]! do
      throw "unsupported fixedpoint option (only :fp.engine spacer/datalog)"
    return { state with script := { script with skipped := script.skipped.push command } }
  | "set-info" =>
    return { state with script := script.add command.text command.source }
  | "declare-rel" =>
    unless args.size == 3 do throw "declare-rel expects a name and argument sorts"
    let key ← symbol args[1]!
    if state.names.contains key then throw s!"duplicate fixedpoint symbol: {key}"
    let sorts ← fields args[2]!
    sorts.forM checkSort
    return { state with
      names := state.names.push key, relations := state.relations.push (key, sorts)
      script := script.add s!"(declare-fun {args[1]!} ({String.intercalate " " sorts.toList}) Bool)" command.source }
  | "declare-var" =>
    unless args.size == 3 do throw "declare-var expects a name and sort"
    let key ← symbol args[1]!
    if state.names.contains key then throw s!"duplicate fixedpoint symbol: {key}"
    checkSort args[2]!
    return { state with
      names := state.names.push key,
      variables := state.variables.push (args[1]!, args[2]!) }
  | "rule" =>
    unless args.size == 2 || args.size == 3 do throw "rule expects a formula and optional name"
    let source ← if args.size == 3 then do
      let label ← symbol args[2]!
      pure { command.source with ruleName := some label }
      else pure command.source
    let bindings := String.intercalate " " (state.variables.toList.map fun (v, s) => s!"({v} {s})")
    let body := if state.variables.isEmpty then args[1]! else s!"(forall ({bindings}) {args[1]!})"
    return { state with script := script.add s!"(assert {body})" source }
  | "query" =>
    unless args.size == 2 do throw "query expects a relation name, without query options"
    let key ← symbol args[1]!
    let some (_, sorts) := state.relations.find? (·.1 == key)
      | throw s!"query expects a declared relation: {key}"
    let arguments := sorts.mapIdx fun i _ => s!"|{stem}.{i}|"
    let bindings := String.intercalate " " ((arguments.zip sorts).toList.map fun (v, s) => s!"({v} {s})")
    let atom := if sorts.isEmpty then args[1]!
      else s!"({args[1]!} {String.intercalate " " arguments.toList})"
    let safety := if sorts.isEmpty then s!"(=> {atom} false)"
      else s!"(forall ({bindings}) (=> {atom} false))"
    return { state with
      queries := state.queries + 1,
      script := ((script.add "(push 1)" command.source).add s!"(assert {safety})" command.source
        |>.add "(check-sat)" command.source).add "(pop 1)" command.source }
  | "exit" =>
    unless args.size == 1 do throw "exit takes no arguments"
    return { state with exited := true }
  | _ => throw s!"unsupported fixedpoint command: {kind}"

/-- `query P` asks whether P is nonempty. Excluding every tuple produces a
safety problem: a model means unreachable; no model means reachable. Only positive
definite rules are accepted, so least-relation semantics agrees with this reduction. -/
def adapt (input : String) (name : String) : Except String Script := do
  let mut reader : Source.Reader input := {}
  let mut state : State := {}
  let mut stem := "smt2lean.query"
  while (Source.tokenize input).any (fun t => t.contains stem) do stem := stem ++ "_"
  while true do
    let (command?, rest) ← (reader.next name).mapError fun e =>
      s!"{name}:{e.position.line}:{e.position.column}: {e.message}"
    reader := rest
    let some source := command? | break
    state ← (command state source stem).mapError fun e => s!"{source.source.context}: {e}"
  if state.queries == 0 then throw s!"{name}: expected at least one fixedpoint query"
  return state.script

/-- False rule heads would make the reachability reduction vacuous. The last
assertion is the adapter's safety condition; all preceding clauses must be definite. -/
def validate (query : Backend.ParsedQuery) : cvc5.Env Chc.Problem := do
  let problem ← Chc.validateQuery query
  for clause in problem.clauses do
    if clause.assertionNumber < query.assertions.size then
      if let .falsity := clause.head then
        let context := clause.source.map (·.context true query.number) |>.getD "fixedpoint"
        throw (.unsupported s!"{context}: fixedpoint rules must have a positive relation head")
  return problem

end Smt2Lean.Fixedpoint
