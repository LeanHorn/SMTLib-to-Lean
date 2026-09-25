import cvc5
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin

/-!
Parse a restricted SMT-LIB script with cvc5 without solving it.

Execute `set-logic` and `assert`; intercept exactly one final `check-sat`.
Pass the captured assertions (`Array cvc5.Term`) and invoked command names
to a callback after the full input has been accepted. Reject other commands
and propagate parsing/invocation errors.

The reconstruction imports register the handlers used by `tests/BackendSmoke.lean`
to translate assertion terms into Lean propositions.
-/

namespace Smt2Lean.Backend

/--
A higher-order function that parses and validates SMT-LIB commands without solving.
Accepts `set-logic`, `assert`, and exactly one final `check-sat`.
Calls the caller's `inspect` function once with all assertion terms and the names
of commands actually executed.
-/
def parseAndInspectQuery
    (input : String)
    (inspect : Array cvc5.Term → Array String → cvc5.Env Unit)
    (name : String := "backend-smoke") : cvc5.Env Unit := do
  let tm      ← cvc5.TermManager.new
  let solver  ← cvc5.Solver.new tm
  let symbols ← cvc5.SymbolManager.new tm
  let parser  ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput input (name := name)
  let mut invoked     : Array String             := #[]
  let mut assertions  : Option (Array cvc5.Term) := none
  while true do
    let cmd ← parser.nextCommand
    if  cmd.isNull then break
    let commandName := cmd.getCommandName
    if assertions.isSome then
      throw (.error s!"{name}: unexpected command after check-sat: {commandName}")
    match commandName with
    | "set-logic" | "assert" =>
      let output ← cmd.invoke solver symbols
      invoked := invoked.push commandName
      -- The binding can report command failures as SMT-LIB output rather than
      -- throwing. Neither supported command should produce other output.
      let response := output.trimAscii.toString
      unless response.isEmpty || response == "success" do
        throw (.error s!"{name}: {commandName}: {response}")
    | "check-sat" =>
      assertions := some (← solver.getAssertions)
    | _ =>
      throw (.unsupported s!"{name}: unsupported command: {commandName}")
  match assertions with
  | none => throw (.error s!"{name}: expected one check-sat")
  | some terms => inspect terms invoked

end Smt2Lean.Backend
