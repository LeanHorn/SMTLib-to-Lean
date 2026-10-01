import Smt2Lean.Backend.Validate

/-!
The native parser only accepts value payloads in constant arrays. A private,
typed store carries each payload through native parsing, including local binders.
Its two private constants are never source declarations or Lean parameters.
-/

namespace Smt2Lean.Backend.ConstantArrays

private inductive SExpr where
  | atom (text : String)
  | list (items : Array SExpr)
  deriving Inhabited

private partial def SExpr.render : SExpr → String
  | .atom text => text
  | .list items => "(" ++ String.intercalate " " (items.toList.map SExpr.render) ++ ")"

private def SExpr.name : SExpr → String
  | .atom text => if text.startsWith "|" then ((text.drop 1).dropEnd 1).toString else text
  | _ => ""

private partial def readExpr (tokens : Array String) (start : Nat) : Except String (SExpr × Nat) := do
  let some token := tokens[start]? | throw "expected an expression"
  if token == ")" then throw "unexpected ')'"
  if token != "(" then return (.atom token, start + 1)
  let mut items := #[]
  let mut next := start + 1
  while tokens[next]? != some ")" do
    let (item, stop) ← readExpr tokens next
    items := items.push item
    next := stop
  return (.list items, next + 1)

structure State where
  nameStem : String
  serial : Nat := 0
  /-- Stable private aliases preserve native sorts when source type names are shadowed. -/
  aliases : Array (cvc5.Sort × String) := #[]
  arrayAlias : Option String := none
  initialized : Bool := false
  constructors : Array ArrayConstructor := #[]

/-- Reserve a prefix absent from every original lexeme, including quoted symbols. -/
def initial (tokens : Array String) : State := Id.run do
  let mut number := 0
  while tokens.any (fun token => (SExpr.atom token).name.startsWith s!"smt2lean.internal.{number}.") do
    number := number + 1
  return { nameStem := s!"smt2lean.internal.{number}." }

private def fresh : StateT State cvc5.Env String := do
  let state ← get
  set { state with serial := state.serial + 1 }
  return s!"{state.nameStem}{state.serial}"

private def invoke (solver : cvc5.Solver) (symbols : cvc5.SymbolManager) (text : String)
    : cvc5.Env Unit := do
  let parser ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput text
  let command ← parser.nextCommand
  let response := (← command.invoke solver symbols).trimAscii.toString
  unless response.isEmpty || response == "success" do throw (.error response)

/-- Capture a sort while its source name still resolves to this native identity. -/
def rememberSort (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (sort : cvc5.Sort) (sortText : String) : StateT State cvc5.Env Unit := do
  let name ← fresh
  invoke solver symbols s!"(define-sort {name} () {sortText})"
  modify fun state => { state with aliases := state.aliases.push (sort, name) }

/-- Initialize aliases only after the source logic is known (or defaults to ALL). -/
def initializeAliases (tm : cvc5.TermManager) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : StateT State cvc5.Env Unit := do
  if (← get).initialized then return
  unless ← symbols.isLogicSet do invoke solver symbols "(set-logic ALL)"
  let logic ← symbols.getLogic
  rememberSort solver symbols (← tm.getBooleanSort) "Bool"
  if logic == "ALL" || logic == "HORN" || logic.contains "IA" || logic.contains "IRA" then
    rememberSort solver symbols (← tm.getIntegerSort) "Int"
  if logic == "ALL" || logic == "HORN" || logic.contains "RA" then
    rememberSort solver symbols (← tm.getRealSort) "Real"
  if logic == "ALL" || logic == "HORN" || logic.startsWith "A" || logic.startsWith "QF_A" then
    let name ← fresh
    invoke solver symbols s!"(define-sort {name} (I E) (Array I E))"
    modify fun state => { state with arrayAlias := some name }
  modify fun state => { state with initialized := true }

private partial def sortSyntax (state : State) (sort : cvc5.Sort) : cvc5.Env String := do
  if let some (_, name) := state.aliases.find? (·.1 == sort) then return name
  if sort.isBitVector then return s!"(_ BitVec {sort.getBitVectorSize!})"
  if sort.isArray then
    let some array := state.arrayAlias | throw (.unsupported "arrays require an array logic")
    return s!"({array} {← sortSyntax state sort.getArrayIndexSort!} {← sortSyntax state sort.getArrayElementSort!})"
  throw (.unsupported s!"unsupported constant-array index sort: {sort}")

private def declare (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (sortText : String) : StateT State cvc5.Env (String × cvc5.Term) := do
  let name ← fresh
  invoke solver symbols s!"(declare-const {name} {sortText})"
  return (name, (← symbols.getDeclaredTerms).back!)

private abbrev Requirements := Array cvc5.Term
private abbrev Bindings := Array (String × Requirements)

private def merge (a b : Requirements) : Requirements :=
  b.foldl (fun result term => if result.contains term then result else result.push term) a

private structure Lowered where
  expression : SExpr
  requirements : Requirements := #[]
  names : Bindings := #[]
  deriving Inhabited

private partial def lower (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (sorts : Array ParsedSort) (bindings : Bindings) (expression : SExpr)
    : StateT State cvc5.Env Lowered := do
  let .list items := expression
    | return { expression, requirements := (bindings.find? (·.1 == expression.name)).map (·.2) |>.getD #[] }
  if let some (SExpr.list qualifier) := items[0]? then
    if qualifier.size == 3 && qualifier[0]!.render == "as" && qualifier[1]!.name == "const" &&
        !bindings.any (·.1 == "const") then
      unless items.size == 2 do throw (.unsupported "constant array expects exactly one payload")
      let (baseName, base) ← declare solver symbols qualifier[2]!.render
      let sort := base.getSort!
      unless sort.isArray && isValueSort sort sorts do
        throw (.unsupported s!"unsupported constant-array sort: {sort}")
      let (indexName, index) ← declare solver symbols (← sortSyntax (← get) sort.getArrayIndexSort!)
      unless index.getSort! == sort.getArrayIndexSort! do
        throw (.error "private constant-array index changed its native sort")
      modify fun state => { state with constructors := state.constructors.push { base, index } }
      let payload ← lower solver symbols sorts bindings items[1]!
      return { payload with
        expression := .list #[.atom "store", .atom baseName, .atom indexName, payload.expression]
        requirements := merge #[base] payload.requirements }
  let head := items[0]?.map SExpr.render |>.getD ""
  if head == "let" && items.size == 3 then
    if let .list bindingsSyntax := items[1]! then
      let mut rewritten := #[]
      let mut locals := #[]
      let mut requirements := #[]
      let mut names := #[]
      let mut globals := bindings
      for binding in bindingsSyntax do
        let .list pair := binding | throw (.error "expected a let binding")
        unless pair.size == 2 do throw (.error "expected a let binding pair")
        let value ← lower solver symbols sorts globals pair[1]!
        rewritten := rewritten.push (.list #[pair[0]!, value.expression])
        locals := locals.push (pair[0]!.name, value.requirements)
        requirements := merge requirements value.requirements
        names := names ++ value.names
        globals := value.names.reverse ++ globals
      let body ← lower solver symbols sorts (locals ++ globals) items[2]!
      return {
        expression := .list #[items[0]!, .list rewritten, body.expression]
        requirements := merge requirements body.requirements
        names := names ++ body.names }
  if (head == "forall" || head == "exists") && items.size == 3 then
    if let .list variables := items[1]! then
      let locals := variables.filterMap fun binder => match binder with
        | .list pair => pair[0]?.map (fun name => (name.name, #[]))
        | _ => none
      let body ← lower solver symbols sorts (locals ++ bindings) items[2]!
      return { body with expression := .list #[items[0]!, items[1]!, body.expression] }
  if head == "!" && items.size >= 2 then
    let body ← lower solver symbols sorts bindings items[1]!
    let mut rewritten := #[items[0]!, body.expression]
    let mut names := body.names
    let mut i := 2
    while i < items.size do
      let some value := items[i + 1]? | throw (.error "expected an annotation value")
      let key := items[i]!
      if key.render == ":named" then
        names := names.push (value.name, body.requirements)
        rewritten := rewritten ++ #[key, value]
      else if key.render == ":pattern" || key.render == ":no-pattern" then
        -- Typecheck lowered hints natively; they add no semantic requirements.
        let hint ← lower solver symbols sorts bindings value
        rewritten := rewritten ++ #[key, hint.expression]
      else rewritten := rewritten ++ #[key, value]
      i := i + 2
    return { body with expression := .list rewritten, names }
  let mut rewritten := #[]
  let mut requirements := #[]
  let mut names := #[]
  let mut visibleBindings := bindings
  for item in items do
    let result ← lower solver symbols sorts visibleBindings item
    rewritten := rewritten.push result.expression
    requirements := merge requirements result.requirements
    names := names ++ result.names
    visibleBindings := result.names.reverse ++ visibleBindings
  return { expression := .list rewritten, requirements, names }

/-- Rewrite only term-bearing commands. Source text and locations remain unchanged. -/
def prepare (command : Source.Command) (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (query : ParsedQuery) : StateT State cvc5.Env (String × Requirements × Bindings) := do
  let tokens := command.tokens
  unless #["assert", "define-fun", "get-value"].contains (tokens[1]?.getD "") do
    return (command.text, #[], #[])
  let (expression, stop) ← match readExpr tokens 0 with
    | .ok result => pure result
    | .error message => throw (.error message)
  unless stop == tokens.size do throw (.error "unexpected trailing tokens")
  let .list items := expression | throw (.error "expected a command")
  let bindings := query.namedArrayConstants.reverse ++
    (knownTerms query).map (fun declaration => (declaration.term.getSymbol!, #[])) ++
    query.datatypes.flatMap (fun group => group.types.flatMap fun datatype =>
      datatype.constructors.map (fun constructor => (constructor.name, #[])))
  if tokens[1]? == some "define-fun" && items.size == 5 then
    let .list parameters := items[2]! | throw (.error "expected definition parameters")
    let locals := parameters.filterMap fun parameter => match parameter with
      | .list pair => pair[0]?.map (fun name => (name.name, #[]))
      | _ => none
    let body ← lower solver symbols query.valueSorts (locals ++ bindings) items[4]!
    return ((SExpr.list (items.set! 4 body.expression)).render, body.requirements, body.names)
  let result ← lower solver symbols query.valueSorts bindings expression
  return (result.expression.render, result.requirements, result.names)

/-- Internal native declarations must never become source parameters. -/
def sourceDeclarations (state : State) (terms : Array cvc5.Term) : Array cvc5.Term :=
  terms.filter fun term => !state.constructors.any (fun c => c.base == term || c.index == term)

end Smt2Lean.Backend.ConstantArrays
