import Smt2Lean.Backend
import Lean.Util.CollectAxioms

open Lean Qq
open Smt2Lean.Backend

private def smokeInput : String :=
  "(set-logic QF_UF)\n(assert (and true (not false)))\n(check-sat)"

private def require (condition : Bool) (message : String) : cvc5.Env Unit := do
  unless condition do throw (.error message)

/-- Check that translation produced the expected closed proposition. -/
private def validateSmokeProp (sort value : Expr)
    (state : Smt.Reconstruct.State) : MetaM Unit := do
  unless state.skippedGoals.isEmpty do
    throwError "reconstruction left unfinished goals"
  for expression in #[sort, value] do
    if expression.hasFVar || expression.hasLooseBVars || expression.hasMVar then
      throwError "reconstruction left unresolved variables"
  unless ← Meta.isDefEq sort q(Prop) do
    throwError "expected SMT Bool to reconstruct as Lean Prop"
  unless ← Meta.isDefEq (← Meta.inferType value) sort do
    throwError "reconstructed assertion has the wrong type"
  unless ← Meta.isDefEq value q(True ∧ ¬False) do
    throwError "expected True ∧ ¬False, got {value}"

/-- Kernel-check and install the definition, then check its axiom dependencies. -/
private def installSmokeDefinition (sort value : Expr) : MetaM Unit := do
  let declaration : Declaration := .defnDecl {
    name        := `BackendSmoke.assertion
    levelParams := []
    type        := sort
    value
    hints       := .abbrev
    safety      := .safe
  }
  -- Check synchronously: a kernel failure must fail this executable.
  let checkedEnv ← ofExceptKernelException <|
    (← getEnv).addDeclCore 0 1000 declaration none
  setEnv checkedEnv
  let axioms ← collectAxioms `BackendSmoke.assertion
  unless axioms.isEmpty do
    throwError "reconstructed definition depends on axioms: {axioms}"
  IO.println s!"Lean definition: def BackendSmoke.assertion : Prop := {← Meta.ppExpr value}"
  IO.println "kernel check passed; no axioms or unfinished goals"

/-- Translate the assertion, then ask Lean's kernel to check its definition. -/
private def checkReconstruction
    (assertion : cvc5.Term) : MetaM Unit := do
  let reconstruction : Smt.ReconstructM (Expr × Expr) := do
    let sort  ← Smt.Reconstruct.reconstructSort (← ofExcept assertion.getSort)
    let value ← Smt.Reconstruct.reconstructTerm assertion
    return (sort, value)
  -- Each reconstruction starts with an empty context and empty caches.
  let ((sort, value), state) ← reconstruction.run {} {}
  validateSmokeProp sort value state
  installSmokeDefinition sort value

private def checkSmoke (env : Environment) : cvc5.Env Unit :=
  parseAndInspectQuery smokeInput fun assertions invoked => do
    require (invoked == #["set-logic", "assert"])
      s!"unexpected native invocation trace: {invoked}"
    require (assertions.size == 1) s!"expected one assertion, got {assertions.size}"
    let assertion := assertions[0]!
    let sort ← ofExcept assertion.getSort
    let kind ← ofExcept assertion.getKind
    require sort.isBoolean "expected a Bool-sorted assertion"
    require (kind == .AND) "expected an AND term"
    let args := assertion.getChildren
    require (args.size == 2) "expected two AND children"
    require (← ofExcept args[0]!.getBooleanValue) "expected true as the first child"
    let rightKind ← ofExcept args[1]!.getKind
    require (rightKind == .NOT) "expected NOT as the second child"
    let negated := args[1]!.getChildren
    require (negated.size == 1) "expected one NOT child"
    require (!(← ofExcept negated[0]!.getBooleanValue)) "expected false inside NOT"
    IO.println s!"invoked commands: {invoked}"
    IO.println "intercepted check-sat; no query invoked"
    IO.println s!"assertion: {assertion} : {sort}"
    IO.println s!"term kinds: {kind}, {← ofExcept args[0]!.getKind}, {rightKind}"
    discard <| (checkReconstruction assertion).toIO
      { fileName := "backend-smoke", fileMap := default } { env }

private def expectFailure (label input : String) : IO Unit := do
  let result ← (parseAndInspectQuery input (fun _ _ => pure ()) (name := label)).run
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted invalid input")
  | .error e => IO.println s!"{label}: rejected as expected: {e}"

def main : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    unsafe enableInitializersExecution
    -- Load the sort/term handlers registered by Backend's imports.
    let env ← importModules #[{ module := `Smt2Lean.Backend }] {} (loadExts := true)
    (checkSmoke env).runIO
    expectFailure "malformed" "(set-logic QF_UF)\n(assert (and true (not false))"
    expectFailure "invalid-logic" "(set-logic NOT_A_LOGIC)\n(check-sat)"
    expectFailure "unsupported-query"
      "(set-logic QF_UF)\n(assert true)\n(check-sat-assuming (true))"
    expectFailure "missing-check" "(set-logic QF_UF)\n(assert true)"
    expectFailure "repeated-check" (smokeInput ++ "\n(check-sat)")
    expectFailure "trailing-command" (smokeInput ++ "\n(assert false)")
    expectFailure "malformed-tail" (smokeInput ++ "\n(assert")
    IO.println "backend parser/reconstruction smoke passed"
    return 0
  catch e =>
    IO.eprintln s!"backend parser/reconstruction smoke failed: {e}"
    return 1
