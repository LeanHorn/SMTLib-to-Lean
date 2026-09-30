import Smt2Lean.Chc
import Smt2Lean.Helpers
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin
import Smt.Reconstruct.Int
import Smt.Reconstruct.UF
import Lean.Util.CollectAxioms

namespace Smt2Lean.Translate

open Lean Meta Qq
open Backend

private def atSource [Monad m] [MonadError m] (source : Option Source.Ref)
    (description : String) (action : m α) (chc : Bool := false) (queryNumber : Nat := 1) : m α := do
  try action
  catch error =>
    let context := source.map (·.context chc queryNumber) |>.getD "translation"
    throwError "{context}: {description}: {error.toMessageData}"

private def checkPropositions (values : Array Expr) (state : Smt.Reconstruct.State)
    : MetaM Unit := do
  unless state.skippedGoals.isEmpty do
    throwError "reconstruction left unfinished goals"
  for value in values do
    if value.hasMVar || value.hasLooseBVars then
      throwError "reconstruction left unresolved variables"
    unless ← isProp value do
      throwError "reconstructed assertion is not a proposition: {value}"

/-- Preserve operator names with transparent, kernel-checked definitions. -/
private def reconstructOperators : Smt.TermReconstructor := fun term => do
  match ← ofExcept term.getKind with
  | .XOR =>
    let helper ← Helpers.xor
    let mut value ← Smt.Reconstruct.reconstructTerm term[0]!
    for child in term.getChildren[1:] do
      value := mkApp2 (mkConst helper) value (← Smt.Reconstruct.reconstructTerm child)
    return value
  | .DISTINCT =>
    let (u, α) ← Smt.Reconstruct.reconstructSortLevelAndSort (← ofExcept term[0]!.getSort)
    let xs ← term.getChildren.mapM Smt.Reconstruct.reconstructTerm
    let helper ← Helpers.distinct xs.size
    return mkAppN (mkApp (mkConst helper [u]) α) xs
  | _ => return none

/-- Bind by native identity so shadowed names cannot capture an outer variable. -/
private def reconstructQuantifier : Smt.TermReconstructor := fun term => do
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

/-- Try our encodings first, then the upstream handlers for the supported theories. -/
@[smt_term_reconstruct] private def reconstructTerm : Smt.TermReconstructor := fun term => do
  for reconstruct in [reconstructOperators, reconstructQuantifier,
      Smt.Reconstruct.Prop.reconstructProp, Smt.Reconstruct.Builtin.reconstructBuiltin,
      Smt.Reconstruct.Int.reconstructInt, Smt.Reconstruct.UF.reconstructUF] do
    if let some value ← reconstruct term then return value
  return none

private def withTermReconstruction (action : MetaM α) : MetaM α := do
  -- Upstream stores handlers in a hash set: registration order is not priority.
  let extension := Smt.Attribute.smtExt
  let previous := (extension.getState (← getEnv)).getD ``Smt.TermReconstructor {}
  modifyEnv fun env => extension.modifyState env fun state =>
    state.insert ``Smt.TermReconstructor {``reconstructTerm}
  try action
  finally
    modifyEnv fun env => extension.modifyState env fun state =>
      state.insert ``Smt.TermReconstructor previous

/-- Fresh carrier parameters, mapped by native sort identity for this query only. -/
private def withCarriers [Inhabited α] (sorts : Array ParsedSort)
    (inspect : Array Expr → Std.HashMap cvc5.Sort Expr → MetaM α) : MetaM α := do
  let declarations ← sorts.mapIdxM fun i _ => do
    return (← mkFreshUserName (Name.mkSimple s!"A{i}"), q(Type))
  withLocalDeclsDND declarations fun carriers => do
    let mut sortCache := {}
    for declaration in sorts, carrier in carriers do
      sortCache := sortCache.insert declaration.sort carrier
    inspect carriers sortCache

/--
Reconstruct a query with carrier parameters followed by declared term parameters.
Use the parameters and assertions inside `inspect`, while their local context exists.
-/
def withAssertions [Inhabited α] (query : ParsedQuery)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α := do
  withCarriers query.sorts fun carriers sortCache => do
    -- Prevent lean-smt's fallback from resolving an unmapped SMT name as a Lean constant.
    for h : i in [:query.assertions.size] do
      atSource query.assertionSources[i]? s!"assertion {i + 1}" (queryNumber := query.number) do
        (validateAssertion query.assertions[i] query.declarations (sorts := query.sorts)).runIO
    let declarations ← query.declarations.mapIdxM fun i (declaration : ParsedDeclaration) =>
      atSource declaration.source s!"declaration '{declaration.name}'" (queryNumber := query.number) do
        let sort ← ofExcept declaration.term.getSort
        let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} { sortCache }
        let stem := if sort.isFunction then "f" else if sort.isBoolean then "p" else "x"
        return (← mkFreshUserName (Name.mkSimple s!"{stem}{i}"), type)
    withLocalDeclsDND declarations fun parameters => do
      let mut userNames : Std.HashMap String Expr := {}
      for declaration in query.declarations, parameter in parameters do
        userNames := userNames.insert (← ofExcept declaration.term.getSymbol) parameter
      let reconstruction : Smt.ReconstructM (Array Expr) := query.assertions.mapIdxM fun i term =>
        atSource query.assertionSources[i]? s!"assertion {i + 1}" (queryNumber := query.number) do
          let value ← Smt.Reconstruct.reconstructTerm term
          checkPropositions #[value] (← get)
          return value
      -- Match the instance scope used when the emitted `if` expressions are elaborated.
      let (assertions, _) ← withTermReconstruction <|
        Elab.Tactic.classical <| reconstruction.run { userNames } { sortCache }
      inspect (carriers ++ parameters) assertions

private def reconstructAtom (relations : Std.HashMap cvc5.Term Expr)
    (atom : Chc.RelationAtom) : Smt.ReconstructM Expr := do
  let some relation := relations[atom.relation.term]?
    | throwError "unmapped CHC relation: {atom.relation.name}"
  return mkAppN relation (← atom.arguments.mapM Smt.Reconstruct.reconstructTerm)

private def reconstructClause (sortCache : Std.HashMap cvc5.Sort Expr)
    (relations : Std.HashMap cvc5.Term Expr)
    (clause : Chc.Clause Chc.Premise) : MetaM Expr := do
  let declarations ← clause.binders.mapM fun (binder : Chc.Binder) => do
    let (type, _) ← (Smt.Reconstruct.reconstructSort binder.sort).run {} { sortCache }
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
    let (value, state) ← withTermReconstruction <|
      Elab.Tactic.classical <| reconstruction.run {} { sortCache, termCache }
    checkPropositions #[value] state
    check value
    return value

/--
Reconstruct CHC clauses with carrier parameters followed by relation parameters.
Each clause is `∀ variables, premise₁ → … → head`. Inspect the parameters and
clauses inside the callback, while their Lean context and native terms are alive.
-/
def withClauses [Inhabited α] (problem : Chc.Problem)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α := do
  withCarriers problem.sorts fun carriers sortCache => do
    let declarations ← problem.relations.mapIdxM fun i (relation : Chc.Relation) =>
      atSource relation.source s!"relation '{relation.name}'" (chc := true) (queryNumber := problem.number) do
        let sort ← ofExcept relation.term.getSort
        let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} { sortCache }
        return (← mkFreshUserName (Name.mkSimple s!"r{i}"), type)
    withLocalDeclsDND declarations fun parameters => do
      let mut relations : Std.HashMap cvc5.Term Expr := {}
      for relation in problem.relations, parameter in parameters do
        relations := relations.insert relation.term parameter
      let clauses ← problem.clauses.mapM fun clause =>
        atSource clause.source s!"clause {clause.assertionNumber}" (chc := true) (queryNumber := problem.number) do
          let value ← reconstructClause sortCache relations clause
          if (← mkForallFVars (carriers ++ parameters) value (usedOnly := false)).hasFVar then
            throwError "clause contains variables outside its interpretation parameters"
          return value
      inspect (carriers ++ parameters) clauses

/-- Permit Lean's foundations, but no admissions or query-specific axioms. -/
def checkStatementAxioms (name : Name) : CoreM Unit := do
  let axioms ← collectAxioms name
  let unexpected := axioms.filter fun dependency =>
    ![``propext, ``Classical.choice, ``Quot.sound].contains dependency
  unless unexpected.isEmpty do
    throwError "{name} depends on unsupported axioms: {unexpected}"

/-- Install a closed proposition after checking its type and axiom dependencies. -/
private def defineProposition (name : Name) (value : Expr) : MetaM Expr := do
  if value.hasFVar || value.hasLooseBVars || value.hasMVar then
    throwError "{name} contains unresolved variables"
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
  withEnv checkedEnv (checkStatementAxioms name)
  setEnv checkedEnv
  return value

/--
Define the refutation over nonempty carriers and declared term interpretations.
No assertions means `True`. Kernel-check the statement without proving it.
-/
def defineRefutation (query : ParsedQuery) (name : Name := `Refutation) : MetaM Expr := do
  let value ← withAssertions query fun parameters assertions => do
    let body ← mkArrow (mkAndN assertions.toList) q(False)
    let carriers := parameters.extract 0 query.sorts.size
    let body ← mkForallFVars (parameters.extract query.sorts.size parameters.size) body (usedOnly := false)
    let body ← carriers.foldrM (init := body) fun carrier body => do
      mkArrow (← mkAppM ``Nonempty #[carrier]) body
    mkForallFVars carriers body (usedOnly := false)
  atSource query.source "Refutation" (defineProposition name value) (queryNumber := query.number)

/--
Define CHC model existence: nonempty carriers and relations satisfying every clause.
Retain unused declarations; no clauses means `True`. Check without proving it.
-/
def defineProblem (problem : Chc.Problem) (name : Name := `Problem) : MetaM Expr := do
  let value ← withClauses problem fun parameters clauses => do
    let carriers := parameters.extract 0 problem.sorts.size
    let relations := parameters.extract problem.sorts.size parameters.size
    let body ← relations.foldrM (init := mkAndN clauses.toList) fun parameter body => do
      mkAppM ``Exists #[← mkLambdaFVars #[parameter] body (usedOnly := false)]
    carriers.foldrM (init := body) fun carrier body => do
      let body := mkApp2 (mkConst ``And) (← mkAppM ``Nonempty #[carrier]) body
      mkAppM ``Exists #[← mkLambdaFVars #[carrier] body (usedOnly := false)]
  atSource problem.source "Problem" (defineProposition name value) (chc := true) (queryNumber := problem.number)

end Smt2Lean.Translate
