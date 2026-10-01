import Smt2Lean.Backend.Types

namespace Smt2Lean.Backend

/-- One native branch; no constructor means its variable binds the whole scrutinee. -/
structure MatchCase where
  binders : Array cvc5.Term
  constructor : Option cvc5.Term
  body : cvc5.Term

/-- Validate patterns and coverage, retaining source order (the first match wins).
Validate branch bodies separately, under their own binders, even if unreachable. -/
def readMatchCases (term : cvc5.Term) : cvc5.Env (Array MatchCase) := do
  unless term.getKind! == .MATCH && term.getNumChildren > 1 && term[0]!.getSort!.isDatatype do
    throw (.unsupported "expected a datatype match with at least one branch")
  let domain := term[0]!.getSort!
  let datatype ← ofExcept domain.getDatatype
  let mut cases := #[]
  let mut covered : Array cvc5.Term := #[]
  let mut catchAll := false
  for branch in term.getChildren[1:] do
    let (binders, pattern, body) ← match branch.getKind!, branch.getChildren with
      | .MATCH_CASE, #[pattern, body] => pure (#[], pattern, body)
      | .MATCH_BIND_CASE, #[variables, pattern, body] => do
        unless variables.getKind! == .VARIABLE_LIST do
          throw (.unsupported "expected match pattern variables")
        pure (variables.getChildren, pattern, body)
      | _, _ => throw (.unsupported "malformed match branch")
    unless pattern.getSort! == domain && body.getSort! == term.getSort! do
      throw (.unsupported "match pattern or result has the wrong sort")
    let mut names : Array String := #[]
    for binder in binders do
      unless binder.getKind! == .VARIABLE do throw (.unsupported "expected a pattern variable")
      let name ← ofExcept binder.getSymbol
      if names.contains name then throw (.unsupported "duplicate match pattern variable")
      names := names.push name
    let constructor ← if pattern.getKind! == .VARIABLE then do
      unless binders == #[pattern] do throw (.unsupported "invalid catch-all pattern")
      catchAll := true
      pure none
    else do
      unless pattern.getKind! == .APPLY_CONSTRUCTOR && pattern.getNumChildren > 0 do
        throw (.unsupported "expected a flat constructor pattern or a variable")
      unless pattern.getChildren.extract 1 pattern.getNumChildren == binders do
        throw (.unsupported "constructor patterns require distinct variables in field order")
      let mut found := false
      for constructor in datatype do
        if (← constructor.getTerm) != pattern[0]! then continue
        unless constructor.getNumSelectors == binders.size do
          throw (.unsupported "wrong constructor pattern arity")
        for h : i in [:constructor.getNumSelectors] do
          unless binders[i]!.getSort! == (← constructor[i].getCodomainSort) do
            throw (.unsupported "wrong constructor pattern field sort")
        found := true
      unless found do throw (.unsupported "match constructor belongs to another datatype")
      covered := covered.push pattern[0]!
      pure (some pattern[0]!)
    cases := cases.push { binders, constructor, body }
  unless catchAll do
    for constructor in datatype do
      unless covered.contains (← constructor.getTerm) do
        throw (.unsupported "non-exhaustive datatype match")
  return cases

end Smt2Lean.Backend
