import Smt2Lean.Backend
import Lean.Util.CollectAxioms

namespace Smt2Lean.Translate

open Lean Meta Qq
open Backend

/--
Reconstruct a parsed query using fresh Prop parameters for its declarations.
Use the parameters and assertions inside `inspect`, while their local context exists.
-/
def withAssertions [Inhabited α] (query : BoolQuery)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α := do
  -- Prevent lean-smt's fallback from resolving an unmapped SMT name as a Lean constant.
  for assertion in query.assertions do
    (validateBooleanTerm assertion query.declarations).runIO
  let declarations ← query.declarations.mapIdxM fun i _ => do
    return (← mkFreshUserName (Name.mkSimple s!"p{i}"), q(Prop))
  withLocalDeclsDND declarations fun parameters => do
    let mut userNames : Std.HashMap String Expr := {}
    for declaration in query.declarations, parameter in parameters do
      userNames := userNames.insert (← ofExcept declaration.term.getSymbol) parameter
    let reconstruction := query.assertions.mapM Smt.Reconstruct.reconstructTerm
    let (assertions, state) ← reconstruction.run { userNames } {}
    unless state.skippedGoals.isEmpty do
      throwError "reconstruction left unfinished goals"
    for assertion in assertions do
      if assertion.hasMVar || assertion.hasLooseBVars then
        throwError "reconstruction left unresolved variables"
      unless ← isProp assertion do
        throwError "reconstructed assertion is not a proposition: {assertion}"
    inspect parameters assertions

/--
Define `Refutation : Prop := ∀ parameters, (assertions) → False` in the Lean environment.
An empty assertion set means `True`. Kernel-check the definition, without proving it.
-/
def defineRefutation (query : BoolQuery) (name : Name := `Refutation) : MetaM Expr := do
  let value ← withAssertions query fun parameters assertions => do
    let body ← mkArrow (mkAndN assertions.toList) q(False)
    mkForallFVars parameters body (usedOnly := false)
  if value.hasFVar || value.hasLooseBVars || value.hasMVar then
    throwError "refutation contains unresolved variables"
  let declaration : Declaration := .defnDecl {
    name
    levelParams := []
    type := q(Prop)
    value
    hints := .abbrev
    safety := .safe
  }
  -- Check synchronously so a kernel failure cannot be reported as success.
  let checkedEnv ← ofExceptKernelException <|
    (← getEnv).addDeclCore 0 1000 declaration none
  setEnv checkedEnv
  let axioms ← collectAxioms name
  unless axioms.isEmpty do
    throwError "refutation depends on axioms: {axioms}"
  return value

end Smt2Lean.Translate
