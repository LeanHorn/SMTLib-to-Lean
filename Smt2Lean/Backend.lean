import cvc5
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin
import Smt.Reconstruct.Int

/-!
Parse a restricted SMT-LIB script with cvc5 without solving it.

Accept one Bool/Int query, with declarations, assertions, and optional metadata.
Intercept `check-sat` and pass the validated query to a callback after reading
the entire input. Report failures with the input name and command number.

The reconstruction imports register the handlers used by `Translate.lean`
and the reconstruction tests to turn assertion terms into Lean propositions.
-/

namespace Smt2Lean.Backend

/-- An SMT name and its native identity. No Lean name has been assigned yet. -/
structure ParsedDeclaration where
  name : String
  term : cvc5.Term

/-- One validated query. Use native terms only inside `inspect`. -/
structure ParsedQuery where
  declarations : Array ParsedDeclaration := #[]
  assertions : Array cvc5.Term := #[]
  invoked : Array String := #[]

/-- Check every node's sort, operator, and declaration identity. -/
def validateAssertion (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) : cvc5.Env Unit := do
  unless (← ofExcept root.getSort).isBoolean do
    throw (.unsupported "expected a Bool assertion")
  let mut pending := #[root]
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    let sort ← ofExcept term.getSort
    unless sort.isBoolean || sort.isInteger do
      throw (.unsupported s!"expected Bool or Int, got {sort}")
    let kind ← ofExcept term.getKind
    let children := term.getChildren
    let validArity ← match kind with
      | .CONST_BOOLEAN | .CONST_INTEGER => pure children.isEmpty
      | .CONSTANT => do
        unless declarations.any (·.term == term) do
          throw (.unsupported s!"undeclared term: {term}")
        pure children.isEmpty
      | .NOT | .NEG => pure (children.size == 1)
      | .AND | .OR | .IMPLIES => pure (children.size >= 2)
      -- cvc5 expands chained equality into a conjunction of binary equalities.
      | .EQUAL => pure (children.size == 2)
      | _ => throw (.unsupported s!"unsupported operator: {kind}")
    unless validArity do
      throw (.unsupported s!"unsupported arity for {kind}: {children.size}")
    pending := pending ++ children

/-- These metadata fields never become assumptions or select a proof target. -/
private def validateMetadata (command : cvc5.Command) : cvc5.Env Unit := do
  -- The binding exposes no command arguments; inspect cvc5's canonical printing.
  let text := command.toString
  let keys := #[":status", ":source", ":category", ":license", ":notes"]
  if keys.any (fun key => text.startsWith s!"(set-info {key} ") then return
  if text == "(set-info :smt-lib-version 2.6)" then return
  throw (.unsupported s!"unsupported metadata: {text}")

private def invokeCommand (command : cvc5.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : cvc5.Env Unit := do
  let response := (← command.invoke solver symbols).trimAscii.toString
  unless response.isEmpty || response == "success" do
    throw (.error s!"{command.getCommandName}: {response}")

private def commandError (name : String) (ordinal : Nat) : cvc5.Error → cvc5.Error
  | .error message => .error s!"{name}: command {ordinal}: {message}"
  | .recoverable message => .recoverable s!"{name}: command {ordinal}: {message}"
  | .unsupported message => .unsupported s!"{name}: command {ordinal}: {message}"
  | .option message => .option s!"{name}: command {ordinal}: {message}"
  | .missingValue => .error s!"{name}: command {ordinal}: missing native value"

/--
A higher-order function that parses and validates SMT-LIB commands without solving.
Accepts supported Bool/Int declarations and assertions, metadata, and one `check-sat`.
Only metadata and an optional final `exit` may follow the check.
Calls `inspect` once with the declarations, assertions, and executed command names.
-/
def parseAndInspectQuery
    (input : String)
    (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String := "backend-smoke") : cvc5.Env Unit := do
  let tm      ← cvc5.TermManager.new
  let solver  ← cvc5.Solver.new tm
  let symbols ← cvc5.SymbolManager.new tm
  let parser  ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput input (name := name)
  let mut query : ParsedQuery := {}
  let mut checked := false
  let mut exited := false
  let mut ordinal := 1
  while true do
    let commandOrdinal := ordinal
    try
      let cmd ← parser.nextCommand
      if cmd.isNull then break
      let commandName := cmd.getCommandName
      if exited then
        throw (.unsupported s!"unexpected command after exit: {commandName}")
      if checked && commandName != "set-info" && commandName != "exit" then
        throw (.unsupported s!"unexpected command after check-sat: {commandName}")
      match commandName with
      | "set-logic" =>
        unless #["QF_UF", "QF_LIA", "QF_NIA", "ALL"].any
            (fun logic => cmd.toString == s!"(set-logic {logic})") do
          throw (.unsupported s!"expected QF_UF, QF_LIA, QF_NIA, or ALL, got {cmd}")
        invokeCommand cmd solver symbols
        query := { query with invoked := query.invoked.push commandName }
      | "declare-const" | "declare-fun" =>
        invokeCommand cmd solver symbols
        let terms ← symbols.getDeclaredTerms
        unless terms.size == query.declarations.size + 1 do
          throw (.error "expected one new declaration")
        let term := terms.back!
        let sort ← ofExcept term.getSort
        unless sort.isBoolean || sort.isInteger do
          throw (.unsupported s!"only nullary Bool/Int declarations are supported, got {sort}")
        let symbol ← ofExcept term.getSymbol
        if query.declarations.any (·.name == symbol) then
          throw (.unsupported s!"duplicate declaration: {symbol}")
        query := { query with
          declarations := query.declarations.push { name := symbol, term }
          invoked := query.invoked.push commandName }
      | "assert" =>
        invokeCommand cmd solver symbols
        let assertions ← solver.getAssertions
        let some term := assertions.back?
          | throw (.error "assert command did not store a formula")
        validateAssertion term query.declarations
        query := { query with invoked := query.invoked.push commandName }
      | "set-info" => validateMetadata cmd
      | "check-sat" =>
        query := { query with assertions := ← solver.getAssertions }
        checked := true
      | "exit" =>
        unless checked do throw (.error "exit before check-sat")
        exited := true
      | _ => throw (.unsupported s!"unsupported command: {commandName}")
      ordinal := ordinal + 1
    catch error => throw (commandError name commandOrdinal error)
  unless checked do
    throw (commandError name ordinal (.error "expected one check-sat"))
  inspect query

end Smt2Lean.Backend
