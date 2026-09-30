import Smt2Lean.Backend.Parser
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin
import Lean.Util.CollectAxioms

open Lean Qq
open Smt2Lean.Backend

/-- Check that translation produced the expected closed proposition. -/
private def checkProposition (sort value : Expr)
    (state : Smt.Reconstruct.State) : MetaM Unit := do
  unless state.skippedGoals.isEmpty do
    throwError "reconstruction left unfinished goals"
  for expression in #[sort, value] do
    if expression.hasFVar || expression.hasLooseBVars || expression.hasMVar then
      throwError "reconstruction left unresolved variables"
  unless ← Meta.isDefEq sort q(Prop) do
    throwError "expected SMT Bool to reconstruct as Lean Prop"
  unless ← Meta.isDefEq value q(True ∧ ¬False) do
    throwError "expected True ∧ ¬False, got {value}"

/-- Kernel-check and install the definition, then check its axiom dependencies. -/
private def checkDefinition (sort value : Expr) : MetaM Unit := do
  let declaration : Declaration := .defnDecl {
    name        := `Reconstruction.assertion
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
  let axioms ← collectAxioms `Reconstruction.assertion
  unless axioms.isEmpty do
    throwError "reconstructed definition depends on axioms: {axioms}"

/-- Translate the assertion, then ask Lean's kernel to check its definition. -/
private def checkReconstruction (assertion : cvc5.Term) : MetaM Unit := do
  let reconstruction : Smt.ReconstructM (Expr × Expr) := do
    let sort  ← Smt.Reconstruct.reconstructSort (← ofExcept assertion.getSort)
    let value ← Smt.Reconstruct.reconstructTerm assertion
    return (sort, value)
  let ((sort, value), state) ← reconstruction.run {} {}
  checkProposition sort value state
  checkDefinition sort value
  IO.println s!"Reconstruction passed: {← Meta.ppExpr value} (kernel checked, no axioms)"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  -- Load the upstream Boolean sort/term handlers explicitly.
  let env ← importModules #[{ module := `Smt.Reconstruct.Prop },
    { module := `Smt.Reconstruct.Builtin }] {} (loadExts := true)
  let input := "(set-logic QF_UF)\n(assert (and true (not false)))\n(check-sat)"
  (parseAndInspectQuery input (name := "reconstruction") fun query => do
    unless query.invoked == #["set-logic", "assert"] do
      throw (.error s!"unexpected native invocation trace: {query.invoked}")
    let #[assertion] := query.assertions
      | throw (.error "expected one assertion")
    discard <| (checkReconstruction assertion).toIO
      { fileName := "reconstruction", fileMap := default } { env }
  ).runIO
