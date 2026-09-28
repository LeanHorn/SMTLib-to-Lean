import Smt2Lean.Backend
import Lean.Util.CollectAxioms

namespace Smt2Lean.Translate

open Lean Meta Qq
open Backend

/-- Bind by native identity so shadowed names cannot capture an outer variable. -/
@[smt_term_reconstruct] private def reconstructQuantifier : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  unless kind == .FORALL || kind == .EXISTS do return none
  let variables := term[0]!.getChildren
  let declarations ← variables.mapM fun (binder : cvc5.Term) => do
    let type ← Smt.Reconstruct.reconstructSort (← ofExcept binder.getSort)
    let name ← mkFreshUserName (Name.mkSimple (← ofExcept binder.getSymbol))
    return (name, type)
  -- Carry outer variable bindings, but discard cached expressions from that scope.
  let bindings := (← get).termCache.filter fun binder _ => binder.getKind! == .VARIABLE
  withLocalDeclsDND declarations fun parameters => Smt.Reconstruct.withNewTermCache do
    let mut cache := bindings
    for binder in variables, parameter in parameters do
      cache := cache.insert binder parameter
    modify fun state => { state with termCache := cache }
    let body ← Smt.Reconstruct.reconstructTerm term[1]!
    if kind == .FORALL then
      return ← mkForallFVars parameters body (usedOnly := false)
    else
      let result ← parameters.foldrM (init := body) fun parameter body => do
        mkAppM ``Exists #[← mkLambdaFVars #[parameter] body]
      return result

/--
Reconstruct a parsed query using fresh parameters of each declaration's Lean type.
Use the parameters and assertions inside `inspect`, while their local context exists.
-/
def withAssertions [Inhabited α] (query : ParsedQuery)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α := do
  -- Prevent lean-smt's fallback from resolving an unmapped SMT name as a Lean constant.
  for assertion in query.assertions do
    (validateAssertion assertion query.declarations).runIO
  let declarations ← query.declarations.mapIdxM fun i (declaration : ParsedDeclaration) => do
    let sort ← ofExcept declaration.term.getSort
    let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} {}
    let stem := if sort.isFunction then "f" else if sort.isBoolean then "p" else "x"
    return (← mkFreshUserName (Name.mkSimple s!"{stem}{i}"), type)
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
def defineRefutation (query : ParsedQuery) (name : Name := `Refutation) : MetaM Expr := do
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
