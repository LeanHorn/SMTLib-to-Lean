import Smt2Lean.Backend.Parser

namespace Smt2Lean.Chc

open Backend

/-- A declared predicate. An empty argument list means a nullary relation. -/
structure Relation extends ParsedDeclaration where
  argumentSorts : Array cvc5.Sort

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
  premises : Array α
  head : ClauseHead

/-- All declarations and clauses have passed validation. Keep native terms in the callback. -/
structure Problem where
  number : Nat := 1
  source : Option Source.Ref := none
  relations : Array Relation
  clauses : Array (Clause Premise)

/-- Collect every declared relation, including unused ones. Use within the parser callback. -/
def collectRelations (declarations : Array ParsedDeclaration) (queryNumber : Nat := 1)
    : cvc5.Env (Array Relation) :=
  declarations.mapM fun declaration => do
    try
      let sort ← ofExcept declaration.term.getSort
      let arguments ← if sort.isFunction then ofExcept sort.getFunctionDomainSorts else pure #[]
      let result ← if sort.isFunction then ofExcept sort.getFunctionCodomainSort else pure sort
      unless result.isBoolean && arguments.all (fun s => s.isBoolean || s.isInteger) do
        throw (.unsupported s!"unsupported CHC declaration '{declaration.name}': expected a Bool-valued relation over Bool/Int, got {sort}")
      return { toParsedDeclaration := declaration, argumentSorts := arguments }
    catch error =>
      throw (declaration.source.map (fun source => errorWithContext (source.context true queryNumber) error)
        |>.getD error)

/-- Arguments and guards may use clause variables and theory terms, but no declared relations. -/
private def checkRelationFree (terms : Array cvc5.Term) (context : String) : cvc5.Env Unit := do
  let mut pending := terms
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    -- In this profile all global symbols are relations; bound variables are VARIABLE.
    let kind ← ofExcept term.getKind
    if kind == .CONSTANT || kind == .APPLY_UF then
      throw (.unsupported s!"CHC relation inside {context}: {term}")
    pending := pending ++ term.getChildren

/-- Recognize an atom in an already parsed/scope-checked term, using native identity. -/
def relationAtom? (relations : Array Relation) (term : cvc5.Term) : cvc5.Env (Option RelationAtom) := do
  let kind ← ofExcept term.getKind
  let (head, arguments) ← match kind with
    | .CONSTANT => pure (term, #[])
    | .APPLY_UF =>
      let children := term.getChildren
      let some head := children[0]? | throw (.unsupported "relation application has no head")
      pure (head, children.extract 1 children.size)
    | _ => return none
  let some relation := relations.find? (·.term == head)
    | throw (.unsupported s!"undeclared CHC relation: {head}")
  unless arguments.size == relation.argumentSorts.size do
    throw (.unsupported s!"wrong argument count for CHC relation '{relation.name}'")
  for argument in arguments, expected in relation.argumentSorts do
    unless (← ofExcept argument.getSort) == expected do
      throw (.unsupported s!"wrong argument sort for CHC relation '{relation.name}': expected {expected}")
  checkRelationFree arguments "a relation argument"
  return some { relation, arguments }

/-- Recognize a bare relation assertion; use extractClause for quantified clauses. -/
def recognizeFact (relations : Array Relation) (assertion : cvc5.Term) : cvc5.Env RelationAtom := do
  let some atom ← relationAtom? relations assertion
    | throw (.unsupported s!"expected a relation fact, got {assertion}")
  return atom

/-- After leading forall binders, every premise and head must be quantifier-free. -/
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
      throw (.unsupported "CHC quantifiers must be leading forall binders")
    pending := pending ++ term.getChildren

/--
Extract leading binders, implication premises, and a relation/false head.
Input must already be parsed and scope-checked. Keep native terms in the callback.
Conjunctions in premises stay intact here; `validateQuery` flattens and classifies them.
-/
def extractClause (relations : Array Relation) (assertionNumber : Nat)
    (assertion : cvc5.Term) (source : Option Source.Ref := none) : cvc5.Env Clause := do
  let mut binders := #[]
  let mut body := assertion
  while (← ofExcept body.getKind) == .FORALL do
    for term in body[0]!.getChildren do
      binders := binders.push { term, sort := ← ofExcept term.getSort : Binder }
    body := body[1]!
  checkNoQuantifiers body
  let mut premises := #[]
  while (← ofExcept body.getKind) == .IMPLIES do
    let children := body.getChildren
    premises := premises ++ children.pop
    body := children.back!
  let falseHead ← if (← ofExcept body.getKind) == .CONST_BOOLEAN then
    Bool.not <$> ofExcept body.getBooleanValue
  else pure false
  let head ← if falseHead then
    pure ClauseHead.falsity
  else do
    let some atom ← relationAtom? relations body
      | throw (.unsupported s!"expected a relation or false as CHC head, got {body}")
    pure (ClauseHead.relation atom)
  return { assertionNumber, source, binders, premises, head }

/-- Flatten only premise conjunctions, keeping source order and other formulas intact. -/
private def validatePremises (relations : Array Relation) (terms : Array cvc5.Term)
    : cvc5.Env (Array Premise) := do
  let mut pending := terms.toList
  let mut premises := #[]
  while !pending.isEmpty do
    let term := pending.head!
    pending := pending.tail!
    if (← ofExcept term.getKind) == .AND then
      pending := term.getChildren.toList ++ pending
    else if let some atom ← relationAtom? relations term then
      premises := premises.push (.relation atom)
    else
      checkRelationFree #[term] "a theory guard"
      premises := premises.push (.guard term)
  return premises

/-- Validate every clause of an already parsed/scope-checked query before returning a problem. -/
def validateQuery (query : ParsedQuery) (name : String := "chc") : cvc5.Env Problem := do
  let relations ← collectRelations query.declarations query.number
  let clauses : Array (Clause Premise) ← query.assertions.mapIdxM fun i assertion => do
    let source := query.assertionSources[i]?
    let context := source.map (·.context true query.number) |>.getD s!"{name}: query {query.number}"
    try
      let clause ← extractClause relations (i + 1) assertion source
      let premises ← validatePremises relations clause.premises
      return {
        assertionNumber := clause.assertionNumber
        source
        binders := clause.binders
        premises
        head := clause.head
      }
    catch error => throw (errorWithContext s!"{context}: clause {i + 1}" error)
  return { number := query.number, source := query.source, relations, clauses }

/-- Parse and validate the whole CHC input, then inspect it once without solving. -/
def parseAndInspectProblem (input : String) (inspect : Problem → cvc5.Env Unit)
    (name : String := "chc") : cvc5.Env Unit :=
  parseAndInspectQuery input (name := name) (mode := .chc) fun query => do
    inspect (← validateQuery query name)

end Smt2Lean.Chc
