import Smt2Lean.Chc
import Lean.Util.CollectAxioms

namespace Smt2Lean.Translate

open Lean Meta Qq
open Backend

private def checkPropositions (values : Array Expr) (state : Smt.Reconstruct.State)
    : MetaM Unit := do
  unless state.skippedGoals.isEmpty do
    throwError "reconstruction left unfinished goals"
  for value in values do
    if value.hasMVar || value.hasLooseBVars then
      throwError "reconstruction left unresolved variables"
    unless ← isProp value do
      throwError "reconstructed assertion is not a proposition: {value}"

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
    checkPropositions assertions state
    inspect parameters assertions

private def reconstructAtom (relations : Std.HashMap cvc5.Term Expr)
    (atom : Chc.RelationAtom) : Smt.ReconstructM Expr := do
  let some relation := relations[atom.relation.term]?
    | throwError "unmapped CHC relation: {atom.relation.name}"
  return mkAppN relation (← atom.arguments.mapM Smt.Reconstruct.reconstructTerm)

private def reconstructClause (relations : Std.HashMap cvc5.Term Expr)
    (clause : Chc.Clause Chc.Premise) : MetaM Expr := do
  let declarations ← clause.binders.mapM fun (binder : Chc.Binder) => do
    let (type, _) ← (Smt.Reconstruct.reconstructSort binder.sort).run {} {}
    let name ← mkFreshUserName (Name.mkSimple (← ofExcept binder.term.getSymbol))
    return (name, type)
  withLocalDeclsDND declarations fun variables => do
    -- Start afresh for each clause: cvc5 can reuse a variable across assertions.
    let mut termCache := relations
    for binder in clause.binders, parameter in variables do
      termCache := termCache.insert binder.term parameter
    let reconstruction : Smt.ReconstructM Expr := do
      let head ← match clause.head with
        | .relation atom => reconstructAtom relations atom
        | .falsity => pure q(False)
      let premises ← clause.premises.mapM fun premise => match premise with
        | .relation atom => reconstructAtom relations atom
        | .guard term => Smt.Reconstruct.reconstructTerm term
      let body ← premises.foldrM (fun premise body => mkArrow premise body) head
      mkForallFVars variables body (usedOnly := false)
    let (value, state) ← reconstruction.run {} { termCache }
    checkPropositions #[value] state
    check value
    return value

/--
Reconstruct validated CHC clauses with fresh relation parameters.
Each clause is `∀ variables, premise₁ → … → head`. Inspect the parameters and
clauses inside the callback, while their Lean context and native terms are alive.
-/
def withClauses [Inhabited α] (problem : Chc.Problem)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let declarations ← problem.relations.mapIdxM fun i (relation : Chc.Relation) => do
    let sort ← ofExcept relation.term.getSort
    let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} {}
    return (← mkFreshUserName (Name.mkSimple s!"r{i}"), type)
  withLocalDeclsDND declarations fun parameters => do
    let mut relations : Std.HashMap cvc5.Term Expr := {}
    for relation in problem.relations, parameter in parameters do
      relations := relations.insert relation.term parameter
    let clauses ← problem.clauses.mapM fun clause => do
      try
        let value ← reconstructClause relations clause
        if (← mkForallFVars parameters value (usedOnly := false)).hasFVar then
          throwError "clause contains variables outside its relation parameters"
        return value
      catch error => throwError "CHC clause {clause.assertionNumber}: {error.toMessageData}"
    inspect parameters clauses

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
