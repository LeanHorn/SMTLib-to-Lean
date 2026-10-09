import Smt2Lean.Chc
import Smt2Lean.Sharing
import Smt2Lean.Statement
import Smt2Lean.SourceBindings
import Smt2Lean.Equivalence
import Smt2Lean.Theory.Arithmetic
import Smt2Lean.Theory.BitVec
import Smt2Lean.Theory.Model
import Smt2Lean.Theory.Match
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
  let binders := term[0]!.getChildren
  let declarations ← binders.mapM fun (binder : cvc5.Term) => do
    let type ← Smt.Reconstruct.reconstructSort (← ofExcept binder.getSort)
    let name ← mkFreshUserName (Name.mkSimple (← ofExcept binder.getSymbol))
    return (name, type)
  -- Carry outer variable bindings, but discard cached compound expressions from that scope.
  let bindings := (← get).termCache.filter fun binder value =>
    binder.getKind! == .VARIABLE || binder.getKind! == .CONSTANT || value.isFVar
  withLocalDeclsDND declarations fun parameters => Smt.Reconstruct.withNewTermCache do
    let mut cache := bindings
    for binder in binders, parameter in parameters do
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
  for reconstruct in [SourceBindings.reconstruct, Datatypes.reconstructTester, Datatypes.reconstructMatch, Selectors.reconstruct,
      Datatypes.reconstruct, Arrays.reconstruct, BitVec.reconstruct, Arithmetic.reconstruct, reconstructOperators, reconstructQuantifier,
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

/-- Permit Lean's foundations, but no admissions or query-specific axioms. -/
def checkStatementAxioms (name : Name) : CoreM Unit := do
  let axioms ← collectAxioms name
  let unexpected := axioms.filter fun dependency =>
    ![``propext, ``Classical.choice, ``Quot.sound].contains dependency
  unless unexpected.isEmpty do
    throwError "{name} depends on unsupported axioms: {unexpected}"

/-- Install a closed definition after checking its type and axiom dependencies. -/
private def defineChecked (name : Name) (value : Expr) : MetaM Expr := do
  if value.hasFVar || value.hasLooseBVars || value.hasMVar then
    throwError "{name} contains unresolved variables"
  let declaration : Declaration := .defnDecl {
    name
    levelParams := []
    type := ← inferType value
    value
    hints := .abbrev
    safety := .safe
  }
  -- Check synchronously so a kernel failure cannot be reported as success.
  let checkedEnv ← ofExceptKernelException <|
    (← getEnv).addDeclCore 0 (Lean.maxRecDepth.get (← getOptions)).toUSize declaration none
  withEnv checkedEnv (checkStatementAxioms name)
  setEnv checkedEnv
  return value

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

/-- Keep source definitions reachable from assertions, in dependency order. -/
private def neededDefinitions (query : ParsedQuery) : Array ParsedDefinition := Id.run do
  let mut pending := query.assertions.map fun a => a.surface.getD a.term
  let mut visited : Std.HashSet cvc5.Term := {}
  let mut used : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    if let some definition := query.definitions.find? (·.symbol == term) then
      used := used.insert term
      pending := pending.push (definition.sourceBody.getD definition.body)
    pending := pending ++ term.getChildren
  return query.definitions.filter (used.contains ·.symbol)

private def reconstructDefinitions (definitions : Array ParsedDefinition) (globals : Array Expr)
    (namespaceName : Name) : Smt.ReconstructM (Array StatementPart) := do
  let mut parts := #[]
  for definition in definitions do
    let binders ← definition.parameters.mapM fun p => do
      return (← mkFreshUserName (Name.mkSimple p.getSymbol!),
        ← Smt.Reconstruct.reconstructSort p.getSort!)
    let saved := (← get).termCache
    let value ← withLocalDeclsDND binders fun parameters => do
      for term in definition.parameters, parameter in parameters do
        modify fun state => { state with termCache := state.termCache.insert term parameter }
      let body ← Smt.Reconstruct.reconstructTerm (definition.sourceBody.getD definition.body)
      mkLambdaFVars parameters body (usedOnly := false)
    modify fun state => { state with termCache := saved }
    let mut value := value
    let mut arguments := #[]
    for parameter in globals.reverse do
      if value.containsFVar parameter.fvarId! then
        value ← mkLambdaFVars #[parameter] value (usedOnly := false)
        arguments := arguments.push parameter
    let base := namespaceName ++ `Definitions ++ Name.mkSimple definition.name
    let name := if (← getEnv).contains base then base.appendIndexAfter definition.source.number else base
    discard <| defineChecked name value
    let call := mkAppN (mkConst name) arguments.reverse
    modify fun state => { state with termCache := state.termCache.insert definition.symbol call }
    parts := parts.push { name, value, source := some definition.source, label := "definition" }
  return parts

/-- Horn normalization can unfold structural macros; emit only definitions still used. -/
private def usedDefinitions (definitions : Array StatementPart) (values : Array Expr)
    : Array StatementPart := Id.run do
  let mut used := values.flatMap Expr.getUsedConstants
  for definition in definitions.reverse do
    if used.contains definition.name then
      used := used ++ definition.value.getUsedConstants
  return definitions.filter (used.contains ·.name)

/-- Reconstruct source and expanded terms in the same interpretation context. -/
private def withAssertionModel [Inhabited α] (query : ParsedQuery)
    (inspect : Array Expr → Array Expr → Array Expr → Array Expr → Array StatementPart → MetaM α)
    (namespaceName : Option Name := none) : MetaM α := do
  withCarriers query.sorts fun carriers sortCache => do
    -- Prevent lean-smt's fallback from resolving an unmapped SMT name as a Lean constant.
    for h : i in [:query.assertions.size] do
      atSource (some query.assertions[i].source) s!"assertion {i + 1}" (queryNumber := query.number) do
        (validateAssertion query.assertions[i].term query.declarations (sorts := query.valueSorts) (constructors := query.arrayConstructors)).runIO
    let definitions := if namespaceName.isSome then neededDefinitions query else #[]
    let roots := query.assertionTerms ++ (if namespaceName.isSome then
      query.assertions.map (fun a => a.surface.getD a.term) ++ definitions.flatMap
        (fun d => #[d.body, d.sourceBody.getD d.body]) else #[])
    Arithmetic.withZeroCases roots fun zeroCases context => do
      let context := SourceBindings.context context query.sourceLets
      Models.withModels query.datatypes (arrayModelTerms query ++ roots) sortCache context (constructors := query.arrayConstructors) fun arrayParameters laws sortCache context => do
        let declarations ← query.declarations.mapIdxM fun i (declaration : ParsedDeclaration) =>
          atSource declaration.source s!"declaration '{declaration.name}'" (queryNumber := query.number) do
            let sort ← ofExcept declaration.term.getSort
            let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} { sortCache }
            let stem := if sort.isFunction then "f" else if sort.isBoolean then "p" else "x"
            return (← mkFreshUserName (Name.mkSimple s!"{stem}{i}"), type)
        withLocalDeclsDND declarations fun parameters => do
          let mut termCache : Std.HashMap cvc5.Term Expr := {}
          for declaration in query.declarations, parameter in parameters do
            termCache := termCache.insert declaration.term parameter
          let allParameters := carriers ++ arrayParameters ++ zeroCases ++ parameters
          let reconstruction : Smt.ReconstructM (Array Expr × Array Expr × Array StatementPart) := do
            let parts ← match namespaceName with
              | some name => reconstructDefinitions definitions allParameters name
              | none => pure #[]
            let assertions ← query.assertions.mapIdxM fun i assertion =>
              atSource (some assertion.source) s!"assertion {i + 1}" (queryNumber := query.number) do
                let term := if namespaceName.isSome then assertion.surface.getD assertion.term else assertion.term
                let value ← Smt.Reconstruct.reconstructTerm term
                checkPropositions #[value] (← get)
                return value
            let originals ← if namespaceName.isSome then
                query.assertionTerms.mapM Smt.Reconstruct.reconstructTerm else pure assertions
            return (assertions, originals, parts)
          -- Match the instance scope used when the emitted `if` expressions are elaborated.
          let ((assertions, originals, parts), _) ← withTermReconstruction <|
            Elab.Tactic.classical <| reconstruction.run context { sortCache, termCache }
          inspect allParameters laws assertions originals parts

/-- Inspect reconstructed assertions while their interpretation parameters are in scope. -/
def withAssertions [Inhabited α] (query : ParsedQuery)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α :=
  withAssertionModel query fun parameters _ assertions _ _ => inspect parameters assertions

private def reconstructAtom (relations : Std.HashMap cvc5.Term Expr)
    (atom : Chc.RelationAtom) : Smt.ReconstructM Expr := do
  let some relation := relations[atom.relation.term]?
    | throwError "unmapped CHC relation: {atom.relation.name}"
  return mkAppN relation (← atom.arguments.mapM Smt.Reconstruct.reconstructTerm)

private def reconstructClause (context : Smt.Reconstruct.Context) (sortCache : Std.HashMap cvc5.Sort Expr)
    (relations : Std.HashMap cvc5.Term Expr)
    (clause : Chc.Clause Chc.Premise) : MetaM Expr := do
  let declarations ← clause.binders.mapM fun (binder : Chc.Binder) => do
    let (type, _) ← (Smt.Reconstruct.reconstructSort binder.sort).run {} { sortCache }
    let name ← mkFreshUserName (Name.mkSimple (← ofExcept binder.term.getSymbol))
    return (name, type)
  withLocalDeclsDND declarations fun locals => do
    -- Start afresh for each clause: cvc5 can reuse a variable across assertions.
    let mut termCache := relations
    for binder in clause.binders, parameter in locals do
      termCache := termCache.insert binder.term parameter
    let body : Smt.ReconstructM Expr := do
      let head ← match clause.head with
        | .relation atom => reconstructAtom relations atom
        | .falsity => pure q(False)
      let premises ← clause.premises.mapM fun premise => match premise with
        | .relation atom => reconstructAtom relations atom
        | .guard term => Smt.Reconstruct.reconstructTerm term
      let body ← premises.foldrM (fun premise body => mkArrow premise body) head
      return body
    let reconstruction : Smt.ReconstructM Expr := do
      let body ← clause.lets.foldr (fun root action => SourceBindings.withBindings (SourceLets.values root) action) body
      mkForallFVars locals body (usedOnly := false)
    let (value, state) ← withTermReconstruction <|
      Elab.Tactic.classical <| reconstruction.run context { sortCache, termCache }
    checkPropositions #[value] state
    check value
    return value

/--
Reconstruct CHC clauses with carriers, array models, arithmetic choices, constants, and relations.
Each clause is `∀ variables, premise₁ → … → head`. Inspect the parameters and
model laws, and clauses inside the callback, while their context and native terms are alive.
-/
private def withClauseModel [Inhabited α] (problem : Chc.Problem)
    (inspect : Array Expr → Array Expr → Array Expr → Array Expr → Array StatementPart → MetaM α)
    (namespaceName : Option Name := none) : MetaM α := do
  withCarriers problem.sorts fun carriers sortCache => do
    let terms := problem.clauses.flatMap fun clause =>
      let premises := clause.premises.flatMap fun premise => match premise with
        | .guard term => #[term]
        | .relation atom => atom.arguments
      premises ++ match clause.head with
        | .falsity => #[]
        | .relation atom => atom.arguments
    let query := problem.query.getD {}
    let definitions := if namespaceName.isSome then neededDefinitions query else #[]
    let terms := terms ++ (if namespaceName.isSome then
      query.assertions.map (fun a => a.surface.getD a.term) ++ definitions.flatMap
        (fun d => #[d.body, d.sourceBody.getD d.body]) else #[])
    Arithmetic.withZeroCases terms fun zeroCases context => do
      let context := SourceBindings.context context query.sourceLets
      let symbols := problem.constants ++ problem.relations.map (·.toParsedDeclaration)
      let modelTerms := problem.arrayTerms ++ symbols.map (·.term) ++ terms ++
        problem.clauses.flatMap (fun c => c.binders.map (·.term))
      Models.withModels problem.datatypes modelTerms sortCache context (constructors := problem.arrayConstructors) fun arrayParameters laws sortCache context => do
        let declarations ← symbols.mapIdxM fun i (symbol : ParsedDeclaration) =>
          atSource symbol.source s!"declaration '{symbol.name}'" (chc := true) (queryNumber := problem.number) do
            let sort ← ofExcept symbol.term.getSort
            let (type, _) ← (Smt.Reconstruct.reconstructSort sort).run {} { sortCache }
            let name := if i < problem.constants.size then s!"c{i}" else s!"r{i - problem.constants.size}"
            return (← mkFreshUserName (Name.mkSimple name), type)
        withLocalDeclsDND declarations fun parameters => do
          -- Every clause and source definition uses the same global interpretation.
          let mut interpretations : Std.HashMap cvc5.Term Expr := {}
          for symbol in symbols, parameter in parameters do
            interpretations := interpretations.insert symbol.term parameter
          let allParameters := carriers ++ arrayParameters ++ zeroCases ++ parameters
          let (definitions, state) ← withTermReconstruction <| Elab.Tactic.classical <|
            (match namespaceName with
              | some name => reconstructDefinitions definitions allParameters name
              | none => pure #[]).run context { sortCache, termCache := interpretations }
          let sourceClauses ← if namespaceName.isSome then (Chc.presentationClauses problem).runIO
            else pure problem.clauses
          let clauses ← sourceClauses.mapM fun clause =>
            atSource clause.source s!"clause {clause.assertionNumber}" (chc := true) (queryNumber := problem.number) do
              let value ← reconstructClause context sortCache state.termCache clause
              if (← mkForallFVars (carriers ++ arrayParameters ++ zeroCases ++ parameters) value (usedOnly := false)).hasFVar then
                throwError "clause contains variables outside its interpretation parameters"
              return value
          let originals ← if namespaceName.isSome then
            problem.clauses.mapM (reconstructClause context sortCache interpretations) else pure clauses
          inspect allParameters laws clauses originals definitions

/-- Inspect reconstructed clauses while their interpretation parameters are in scope. -/
def withClauses [Inhabited α] (problem : Chc.Problem)
    (inspect : Array Expr → Array Expr → MetaM α) : MetaM α :=
  withClauseModel problem fun parameters _ clauses _ _ => inspect parameters clauses

private def defineProposition (name : Name) (value : Expr) : MetaM Expr := do
  defineChecked name (← Sharing.introduce value)

/-- Name each component, closing over just its used parameters and their dependencies. -/
private def nameParts (parameters values : Array Expr) (sources : Array (Option Source.Ref))
    (namespaceName : Name) (label : String) : MetaM (Array Expr × Array StatementPart) := do
  let mut applications := #[]
  let mut parts := #[]
  for original in values, i in [:values.size] do
    let mut value ← Sharing.introduce original
    let mut arguments := #[]
    for parameter in parameters.reverse do
      if value.containsFVar parameter.fvarId! then
        value ← mkLambdaFVars #[parameter] value (usedOnly := false)
        arguments := arguments.push parameter
    let digits := toString (i + 1)
    let padded := String.ofList (List.replicate (3 - digits.length) '0') ++ digits
    let name := namespaceName ++ Name.mkSimple (label ++ padded)
    discard <| defineChecked name value
    applications := applications.push (mkAppN (mkConst name) arguments.reverse)
    parts := parts.push { name, value, source := sources[i]?.getD none, label := s!"{label.toLower} {i + 1}" }
  return (applications, parts)

private def closeRefutation (sortCount : Nat) (parameters laws assertions : Array Expr) : MetaM Expr := do
  let body ← mkArrow (mkAndN assertions.toList) q(False)
  let body ← if laws.isEmpty then pure body else mkArrow (mkAndN laws.toList) body
  let carriers := parameters.extract 0 sortCount
  let body ← mkForallFVars (parameters.extract sortCount parameters.size) body (usedOnly := false)
  let body ← carriers.foldrM (init := body) fun carrier body => do
    mkArrow (← mkAppM ``Nonempty #[carrier]) body
  mkForallFVars carriers body (usedOnly := false)

private def closeProblem (sortCount : Nat) (parameters laws clauses : Array Expr) : MetaM Expr := do
  let carriers := parameters.extract 0 sortCount
  let interpretations := parameters.extract sortCount parameters.size
  let body ← interpretations.foldrM (init := mkAndN (laws.toList ++ clauses.toList)) fun parameter body => do
    mkAppM ``Exists #[← mkLambdaFVars #[parameter] body (usedOnly := false)]
  carriers.foldrM (init := body) fun carrier body => do
    let body := mkApp2 (mkConst ``And) (← mkAppM ``Nonempty #[carrier]) body
    mkAppM ``Exists #[← mkLambdaFVars #[carrier] body (usedOnly := false)]

/-- The kernel checks that naming components preserves the original proposition. -/
private def checkAssembly (name : Name) (original assembled : Expr) : MetaM Unit :=
    withCurrHeartbeats <| withTheReader Core.Context (fun context =>
      let limit := if context.maxHeartbeats == 0 then 0
        else max context.maxHeartbeats (Core.getMaxHeartbeats (maxHeartbeats.set {} 1000000))
      { context with maxHeartbeats := limit }) do
  -- Large queries need room for the expanded reference's congruence proof.
  let declaration : Declaration := .thmDecl {
    name := name ++ `assembly_eq
    levelParams := []
    type := mkApp2 (mkConst ``Iff) original assembled
    value := ← mkAppM ``Iff.of_eq #[← Equivalence.prove original assembled (name.isPrefixOf ·)] }
  discard <| ofExceptKernelException <|
    (← getEnv).addDeclCore 0 (Lean.maxRecDepth.get (← getOptions)).toUSize declaration none

/--
Define the refutation over admissible models and declared terms.
An empty assertion conjunction is `True`. Check the statement without proving it.
-/
def defineRefutation (query : ParsedQuery) (name : Name := `Refutation) : MetaM Expr := do
  let value ← withAssertionModel query fun parameters laws assertions _ _ => do
    closeRefutation query.sorts.size parameters laws assertions
  atSource query.source "Refutation" (defineProposition name value) (queryNumber := query.number)

/--
Define CHC model existence over admissible models, global constants, and relations.
Retain unused declarations; an empty clause conjunction is `True`. Check without proving it.
-/
def defineProblem (problem : Chc.Problem) (name : Name := `Problem) : MetaM Expr := do
  let value ← withClauseModel problem fun parameters laws clauses _ _ => do
    closeProblem problem.sorts.size parameters laws clauses
  atSource problem.source "Problem" (defineProposition name value) (chc := true) (queryNumber := problem.number)

/-- Keep assertion boundaries through emission; the original model quantifiers are unchanged. -/
def refutationStatement (query : ParsedQuery) (name : Name := `Refutation) : MetaM Statement :=
  atSource query.source "Refutation" (queryNumber := query.number) <|
    withAssertionModel query (namespaceName := some name) fun parameters laws assertions originals definitions => do
      let original ← closeRefutation query.sorts.size parameters laws originals
      let (calls, parts) ← nameParts parameters assertions (query.assertionSources.map some) name "Assertion"
      let parts := parts.mapIdx fun i part =>
        if i < assertions.size - query.assumptionCount then part else
          { part with label := s!"assumption {i + 1 - (assertions.size - query.assumptionCount)}" }
      let value ← defineProposition name (← closeRefutation query.sorts.size parameters laws calls)
      checkAssembly name original value
      return { value, parts, definitions := usedDefinitions definitions (parts.map (·.value)) }

/-- Expose parameterized clauses, then existentially close their shared interpretation. -/
def problemStatement (problem : Chc.Problem) (name : Name := `Problem) : MetaM Statement :=
  atSource problem.source "Problem" (chc := true) (queryNumber := problem.number) <|
    withClauseModel problem (namespaceName := some name) fun parameters laws clauses originals definitions => do
      let original ← closeProblem problem.sorts.size parameters laws originals
      let (calls, parts) ← nameParts parameters clauses (problem.clauses.map (·.source)) name "Clause"
      let clauseName := name ++ `Clauses
      let clauseValue ← mkLambdaFVars parameters (mkAndN calls.toList) (usedOnly := false)
      discard <| defineChecked clauseName clauseValue
      let clauseCall := mkAppN (mkConst clauseName) parameters
      let value ← defineProposition name (← closeProblem problem.sorts.size parameters laws #[clauseCall])
      checkAssembly name original value
      let parts := parts.push { name := clauseName, value := clauseValue, label := "clauses" }
      return { value, parts, definitions := usedDefinitions definitions (parts.map (·.value)) }

end Smt2Lean.Translate
