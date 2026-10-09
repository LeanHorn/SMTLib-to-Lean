import Smt2Lean.Backend.Parser

namespace Smt2Lean.Chc

open Backend

/-- A declared predicate. An empty argument list means a nullary relation. -/
structure Relation extends ParsedDeclaration where
  argumentSorts : Array cvc5.Sort

/-- CHC symbol roles. Bool-valued declarations are always relations. -/
inductive Symbol where
  | relation (value : Relation)
  | dataConstant (declaration : ParsedDeclaration) (sort : cvc5.Sort)
  | backgroundFunction (declaration : ParsedDeclaration)
      (argumentSorts : Array cvc5.Sort) (resultSort : cvc5.Sort)

/-- Classify by native sort; this does not validate translation support. -/
def classifyDeclaration (declaration : ParsedDeclaration) : cvc5.Env Symbol := do
  let sort ← ofExcept declaration.term.getSort
  let arguments ← if sort.isFunction then ofExcept sort.getFunctionDomainSorts else pure #[]
  let result ← if sort.isFunction then ofExcept sort.getFunctionCodomainSort else pure sort
  if result.isBoolean then
    return .relation { toParsedDeclaration := declaration, argumentSorts := arguments }
  else if sort.isFunction then
    return .backgroundFunction declaration arguments result
  else
    return .dataConstant declaration sort

/-- A relation applied to ordered arguments. Alone, it is a fact with no premises. -/
structure RelationAtom where
  relation : Relation
  arguments : Array cvc5.Term

/-- One universal variable, retaining its native identity and sort. -/
structure Binder where
  term : cvc5.Term
  sort : cvc5.Sort

inductive ClauseHead where
  | relation (atom : RelationAtom)
  | falsity

/-- A premise is either a positive relation call or a relation-free theory formula. -/
inductive Premise where
  | relation (atom : RelationAtom)
  | guard (term : cvc5.Term)

/-- Extracted clauses contain raw terms; validated clauses contain `Premise`s. -/
structure Clause (α : Type := cvc5.Term) where
  /-- One-based position in the source assertions. -/
  assertionNumber : Nat
  source : Option Source.Ref := none
  binders : Array Binder
  lets : Array cvc5.Term := #[]
  premises : Array α
  head : ClauseHead

/-- All declarations and clauses have passed validation. Keep native terms in the callback. -/
structure Problem where
  query : Option ParsedQuery := none
  number : Nat := 1
  source : Option Source.Ref := none
  sorts : Array ParsedSort := #[]
  datatypes : Array DatatypeGroup := #[]
  /-- Retain array theory requirements from unused definitions and discarded source terms. -/
  arrayTerms : Array cvc5.Term := #[]
  arrayConstructors : Array ArrayConstructor := #[]
  constants : Array ParsedDeclaration := #[]
  functions : Array ParsedDeclaration := #[]
  relations : Array Relation
  clauses : Array (Clause Premise)

/-- Validate and partition declarations, retaining unused symbols and native identities. -/
def collectDeclarations (declarations : Array ParsedDeclaration) (queryNumber : Nat := 1)
    (sorts : Array ParsedSort := #[])
    : cvc5.Env (Array ParsedDeclaration × Array ParsedDeclaration × Array Relation) := do
  let mut constants := #[]
  let mut functions := #[]
  let mut relations := #[]
  for declaration in declarations do
    try
      match ← classifyDeclaration declaration with
      | .relation relation =>
        if relation.argumentSorts.all (isValueSort · sorts) then
          relations := relations.push relation
          continue
      | .dataConstant constant sort =>
        if isValueSort sort sorts then
          constants := constants.push constant
          continue
      | .backgroundFunction function arguments result =>
        if !arguments.isEmpty && arguments.all (isValueSort · sorts) && isValueSort result sorts then
          functions := functions.push function
          continue
      let sort ← ofExcept declaration.term.getSort
      throw (.unsupported s!"unsupported CHC declaration '{declaration.name}': expected a relation, data constant, or first-order background function over supported value sorts, got {sort}")
    catch error =>
      throw (declaration.source.map (fun source => errorWithContext (source.context true queryNumber) error)
        |>.getD error)
  return (constants, functions, relations)

/-- Collect relations after validating all declarations. -/
def collectRelations (declarations : Array ParsedDeclaration) (queryNumber : Nat := 1)
    (sorts : Array ParsedSort := #[]) : cvc5.Env (Array Relation) := do
  return (← collectDeclarations declarations queryNumber sorts).2.2

/-- Permit theory terms and background symbols, but reject relations anywhere inside them. -/
private def checkRelationFree (relations : Array Relation) (terms : Array cvc5.Term) (context : String)
    (constructors : Array ArrayConstructor := #[])
    (background : Array ParsedDeclaration := #[]) : cvc5.Env Unit := do
  let mut pending := terms
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    if constructors.any (·.matches term) then
      pending := pending.push term[2]!
      continue
    let kind ← ofExcept term.getKind
    if kind == .CONSTANT || kind == .APPLY_UF then
      let children := term.getChildren
      let head ← if kind == .CONSTANT then pure term else
        match children[0]? with
        | some head => pure head
        | none => throw (.unsupported "CHC function application has no head")
      if relations.any (·.term == head) then
        throw (.unsupported s!"CHC relation inside {context}: {term}")
      unless background.any (·.term == head) do
        throw (.unsupported s!"undeclared CHC symbol inside {context}: {head}")
      if kind == .CONSTANT then
        if (← ofExcept head.getSort).isFunction then
          throw (.unsupported s!"bare CHC function inside {context}: {head}")
      else
        -- Only skip the declared function head; inspect every argument recursively.
        pending := pending ++ children.extract 1 children.size
      continue
    pending := pending ++ term.getChildren

/-- Quantifiers remain unsupported in relation arguments and residual clause heads. -/
private def checkNoQuantifiers (root : cvc5.Term) : cvc5.Env Unit := do
  let mut pending := #[root]
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    let kind ← ofExcept term.getKind
    if kind == .FORALL || kind == .EXISTS then
      throw (.unsupported "CHC quantifiers require leading forall binders or relation-free theory guards")
    pending := pending ++ term.getChildren

/-- Recognize an atom in an already parsed/scope-checked term, using native identity. -/
def relationAtom? (relations : Array Relation) (term : cvc5.Term)
    (constructors : Array ArrayConstructor := #[])
    (definitions : Array ParsedDefinition := #[]) (alreadyValidated : Bool := false)
    (background : Array ParsedDeclaration := #[]) : cvc5.Env (Option RelationAtom) := do
  let kind ← ofExcept term.getKind
  let (head, arguments) ← match kind with
    | .CONSTANT => pure (term, #[])
    | .APPLY_UF =>
      let children := term.getChildren
      let some head := children[0]? | throw (.unsupported "relation application has no head")
      pure (head, children.extract 1 children.size)
    | _ => return none
  if definitions.any (·.symbol == head) then return none
  if background.any (·.term == head) then return none
  let some relation := relations.find? (·.term == head)
    | throw (.unsupported s!"undeclared CHC symbol: {head}")
  unless arguments.size == relation.argumentSorts.size do
    throw (.unsupported s!"wrong argument count for CHC relation '{relation.name}'")
  for argument in arguments, expected in relation.argumentSorts do
    unless (← ofExcept argument.getSort) == expected do
      throw (.unsupported s!"wrong argument sort for CHC relation '{relation.name}': expected {expected}")
  unless alreadyValidated do
    for argument in arguments do checkNoQuantifiers argument
    checkRelationFree relations arguments "a relation argument" constructors background
  return some { relation, arguments }

/-- Recognize a bare relation assertion; use extractClause for quantified clauses. -/
def recognizeFact (relations : Array Relation) (assertion : cvc5.Term)
    (background : Array ParsedDeclaration := #[]) : cvc5.Env RelationAtom := do
  let some atom ← relationAtom? relations assertion (background := background)
    | throw (.unsupported s!"expected a relation fact, got {assertion}")
  return atom

/-- Nested guard quantifiers may bind theory variables, but cannot enclose relations. -/
private def checkGuardQuantifiers (relations : Array Relation) (terms : Array cvc5.Term)
    (constructors : Array ArrayConstructor) (background : Array ParsedDeclaration) : cvc5.Env Unit := do
  let mut pending := terms
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    let kind ← ofExcept term.getKind
    if kind == .FORALL || kind == .EXISTS then
      checkRelationFree relations #[term] "a quantified theory guard" constructors background
    else
      pending := pending ++ term.getChildren

/-- Expose only clause structure; keep atomic theory calls available for emission. -/
private partial def expose (relations : Array Relation) (query : Option ParsedQuery) (term : cvc5.Term)
    (background : Array ParsedDeclaration)
    : cvc5.Env (cvc5.Term × Array cvc5.Term) := do
  let some query := query | return (term, #[])
  if (SourceLets.root? query.sourceLets term).isSome then
    let (body, lets) ← expose relations (some query) term[1]! background
    return (body, #[term] ++ lets)
  let some tm := query.manager | return (term, #[])
  let body? ← if term.getKind! == .ITE && term[1]! == term[2]! &&
      (SourceLets.markers query.sourceLets).contains term[0]! then
    pure (some term[1]!)
  else unfoldDefinition tm query.definitions term
  if let some body := body? then
    let expanded ← SourceLets.erase tm query.sourceLets term >>= expandDefinitions tm query.definitions
    unless #[cvc5.Kind.AND, .OR, .NOT, .IMPLIES, .FORALL, .EXISTS, .CONST_BOOLEAN].contains expanded.getKind! do
      try
        checkRelationFree relations #[expanded] "a theory guard" query.arrayConstructors background
        return (term, #[])
      catch _ => pure ()
    return ← expose relations (some query) body background
  return (term, #[])

/--
Extract one clause, accepting implication or disjunction syntax.
Negative disjuncts become premises; theory heads become negated guards leading to false.
Input must already be parsed and scope-checked. Keep native terms in the callback.
-/
def extractClause (relations : Array Relation) (assertionNumber : Nat)
    (assertion : cvc5.Term) (source : Option Source.Ref := none)
    (constructors : Array ArrayConstructor := #[])
    (presentation : Option ParsedQuery := none)
    (background : Array ParsedDeclaration := #[]) : cvc5.Env Clause := do
  let mut binders := #[]
  let mut body := assertion
  let mut lets := #[]
  while true do
    let (exposed, added) ← expose relations presentation body background
    body := exposed
    lets := lets ++ added
    unless body.getKind! == .FORALL do break
    for term in body[0]!.getChildren do
      binders := binders.push { term, sort := ← ofExcept term.getSort : Binder }
    body := body[1]!
  let mut premises := #[]
  while true do
    let (exposed, added) ← expose relations presentation body background
    body := exposed
    lets := lets ++ added
    unless body.getKind! == .IMPLIES do break
    let children := body.getChildren
    premises := premises ++ children.pop
    body := children.back!
  let mut pending := [body]
  let mut positiveHead : Option RelationAtom := none
  while !pending.isEmpty do
    let (term, added) ← expose relations presentation pending.head! background
    lets := lets ++ added
    pending := pending.tail!
    let kind ← ofExcept term.getKind
    if kind == .OR then
      pending := term.getChildren.toList ++ pending
    else if kind == .NOT then
      premises := premises.push term[0]!
    else if kind == .CONST_BOOLEAN then
      if ← ofExcept term.getBooleanValue then
        premises := premises.push (← term.notTerm)
    else if let some atom ← relationAtom? relations term constructors
        (presentation.map (·.definitions) |>.getD #[]) presentation.isSome background then
      if positiveHead.isSome then
        throw (.unsupported "multiple positive relations as CHC head")
      positiveHead := some atom
    else
      if presentation.isNone then
        checkNoQuantifiers term
        checkRelationFree relations #[term] "a CHC head" constructors background
      premises := premises.push (← term.notTerm)
  if presentation.isNone then checkGuardQuantifiers relations premises constructors background
  let head := positiveHead.map ClauseHead.relation |>.getD .falsity
  return { assertionNumber, source, binders, lets, premises, head }

/-- Split assertion conjunctions without distributing disjunctions or changing binder identity. -/
def extractClauses (relations : Array Relation) (assertionNumber : Nat)
    (assertion : cvc5.Term) (source : Option Source.Ref := none)
    (constructors : Array ArrayConstructor := #[])
    (presentation : Option ParsedQuery := none)
    (background : Array ParsedDeclaration := #[]) : cvc5.Env (Array Clause) := do
  let mut pending : List (Array Binder × Array cvc5.Term × cvc5.Term) := [(#[], #[], assertion)]
  let mut clauses := #[]
  while !pending.isEmpty do
    let (binders, lets, raw) := pending.head!
    let (term, added) ← expose relations presentation raw background
    let lets := lets ++ added
    pending := pending.tail!
    match ← ofExcept term.getKind with
    | .FORALL =>
      let variables ← term[0]!.getChildren.mapM fun binder => do
        return { term := binder, sort := ← ofExcept binder.getSort : Binder }
      pending := (binders ++ variables, lets, term[1]!) :: pending
    | .AND => pending := term.getChildren.toList.map (binders, lets, ·) ++ pending
    | _ =>
      let clause ← extractClause relations assertionNumber term source constructors presentation background
      clauses := clauses.push { clause with binders := binders ++ clause.binders, lets := lets ++ clause.lets }
  return clauses

/-- Flatten only premise conjunctions, keeping source order and other formulas intact. -/
private def validatePremises (relations : Array Relation) (terms : Array cvc5.Term)
    (constructors : Array ArrayConstructor) (presentation : Option ParsedQuery := none)
    (background : Array ParsedDeclaration := #[]) : cvc5.Env (Array Premise × Array cvc5.Term) := do
  let mut pending := terms.toList
  let mut premises := #[]
  let mut lets := #[]
  while !pending.isEmpty do
    let (term, added) ← expose relations presentation pending.head! background
    lets := lets ++ added
    pending := pending.tail!
    if (← ofExcept term.getKind) == .AND then
      pending := term.getChildren.toList ++ pending
    else if let some atom ← relationAtom? relations term constructors
        (presentation.map (·.definitions) |>.getD #[]) presentation.isSome background then
      premises := premises.push (.relation atom)
    else
      if presentation.isNone then checkRelationFree relations #[term] "a theory guard" constructors background
      premises := premises.push (.guard term)
  return (premises, lets)

/-- Validate every clause of an already parsed/scope-checked query before returning a problem. -/
def validateQuery (query : ParsedQuery) (name : String := "chc") : cvc5.Env Problem := do
  let (constants, functions, relations) ← collectDeclarations query.declarations query.number query.valueSorts
  let background := constants ++ functions
  let mut clauses : Array (Clause Premise) := #[]
  for h : i in [:query.assertions.size] do
    let assertion := query.assertions[i]
    let source := some assertion.source
    let context := source.map (·.context true query.number) |>.getD s!"{name}: query {query.number}"
    try
      for clause in ← extractClauses relations (i + 1) assertion.term source query.arrayConstructors (background := background) do
        let (premises, _) ← validatePremises relations clause.premises query.arrayConstructors (background := background)
        clauses := clauses.push {
          assertionNumber := clause.assertionNumber
          source
          binders := clause.binders
          premises
          head := clause.head
        }
    catch error => throw (errorWithContext s!"{context}: clause {i + 1}" error)
  return {
    query := some query, number := query.number, source := query.source, sorts := query.sorts, datatypes := query.datatypes
    arrayTerms := arrayModelTerms query, arrayConstructors := query.arrayConstructors, constants, functions, relations, clauses }

/-- Reuse validation above, but preserve theory calls and lets in the emitted clauses. -/
def presentationClauses (problem : Problem) : cvc5.Env (Array (Clause Premise)) := do
  let some query := problem.query | return problem.clauses
  let background := problem.constants ++ problem.functions
  let mut result := #[]
  for assertion in query.assertions, i in [:query.assertions.size] do
    for clause in ← extractClauses problem.relations (i + 1) (assertion.surface.getD assertion.term)
        (some assertion.source) query.arrayConstructors (some query) background do
      let (premises, lets) ← validatePremises problem.relations clause.premises query.arrayConstructors (some query) background
      result := result.push { clause with premises, lets := clause.lets ++ lets }
  unless result.size == problem.clauses.size do
    throw (.error "source-preserving clause normalization changed the clause count")
  return result

/-- Parse and validate the whole CHC input, then inspect it once without solving. -/
def parseAndInspectProblem (input : String) (inspect : Problem → cvc5.Env Unit)
    (name : String := "chc") : cvc5.Env Unit :=
  parseAndInspectQuery input (name := name) (mode := .chc) fun query => do
    inspect (← validateQuery query name)

end Smt2Lean.Chc
