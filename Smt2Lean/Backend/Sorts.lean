import Smt2Lean.Backend.Types

namespace Smt2Lean.Backend

/-- Collect ground applications by native identity. Different applications are
independent nonempty carriers; a sort constructor itself is not a value sort. -/
def ParsedQuery.collectSorts (query : ParsedQuery) (roots : Array cvc5.Sort)
    (source : Source.Ref) : cvc5.Env ParsedQuery := do
  let mut pending := roots
  let mut visited : Std.HashSet cvc5.Sort := {}
  let mut instances := query.sortInstances
  while !pending.isEmpty do
    let sort := pending.back!
    pending := pending.pop
    if visited.contains sort then continue
    visited := visited.insert sort
    if sort.isUninterpretedSort && sort.isInstantiated then
      unless instances.any (·.sort == sort) do
        instances := instances.push { name := sort.toString, sort, source := some source }
      pending := pending ++ (← ofExcept sort.getInstantiatedParameters)
    else if sort.isArray then
      pending := pending ++ #[sort.getArrayIndexSort!, sort.getArrayElementSort!]
    else if sort.isFunction then
      pending := pending ++ sort.getFunctionDomainSorts! ++ #[sort.getFunctionCodomainSort!]
    else if sort.isDatatype then
      for constructor in ← ofExcept sort.getDatatype do
        for selector in constructor do
          pending := pending.push (← selector.getCodomainSort)
  return { query with sortInstances := instances }

/-- Include binder and erased-term sorts before checking the supported fragment. -/
def ParsedQuery.collectTermSorts (query : ParsedQuery) (roots : Array cvc5.Term)
    (source : Source.Ref) : cvc5.Env ParsedQuery := do
  let mut pending := roots
  let mut visited : Std.HashSet cvc5.Term := {}
  let mut sorts := #[]
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    sorts := sorts.push (← ofExcept term.getSort)
    pending := pending ++ term.getChildren
    if term.isConstArray then pending := pending.push term.getConstArrayBase!
  query.collectSorts sorts source

end Smt2Lean.Backend
