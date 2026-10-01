import Smt2Lean.Backend.Validate
import Smt2Lean.Backend.Hints

namespace Smt2Lean.Backend

private def rebuild (tm : cvc5.TermManager) (term : cvc5.Term)
    (children : Array cvc5.Term) : cvc5.Env cvc5.Term := do
  if children == term.getChildren then return term
  tm.mkTermOfOp (← ofExcept term.getOp) children

/-- Substitute by native identity; fresh binders prevent arguments from being captured. -/
private partial def instantiate (tm : cvc5.TermManager) (term : cvc5.Term)
    (variables values : Array cvc5.Term)
    : StateT (Std.HashMap (cvc5.Term × Array cvc5.Term × Array cvc5.Term) cvc5.Term)
        cvc5.Env cvc5.Term := do
  if let some i := variables.findIdx? (· == term) then return values[i]!
  let key := (term, variables, values)
  if let some result := (← get)[key]? then return result
  let kind ← ofExcept term.getKind
  let result ← if kind == .FORALL || kind == .EXISTS || kind == .MATCH_BIND_CASE then do
    let old := term[0]!.getChildren
    let fresh ← old.mapM fun v => do tm.mkVar (← ofExcept v.getSort) (← ofExcept v.getSymbol)
    let children ← (term.getChildren.extract 1 term.getNumChildren).mapM fun child =>
      instantiate tm child (old ++ variables) (fresh ++ values)
    tm.mkTerm kind (#[← tm.mkTerm .VARIABLE_LIST fresh] ++ children)
  else
    rebuild tm term (← term.getChildren.mapM fun c => instantiate tm c variables values)
  modify (·.insert key result)
  return result

private partial def expand (tm : cvc5.TermManager) (definitions : Array ParsedDefinition)
    (term : cvc5.Term) : StateT (Std.HashMap cvc5.Term cvc5.Term) cvc5.Env cvc5.Term := do
  if let some result := (← get)[term]? then return result
  let kind ← ofExcept term.getKind
  let head := if kind == .APPLY_UF then term[0]! else term
  let result ← match definitions.find? (·.symbol == head) with
    | some definition => do
      let arguments ← if kind == .APPLY_UF then
          (term.getChildren.extract 1 term.getNumChildren).mapM (expand tm definitions)
        else pure #[]
      unless arguments.size == definition.parameters.size do
        throw (.unsupported s!"wrong argument count for definition: {head}")
      return (← (instantiate tm definition.body definition.parameters arguments).run {}).1
    | none => rebuild tm term (← term.getChildren.mapM (expand tm definitions))
  modify (·.insert term result)
  return result

/-- Expand checked definitions without solving or simplifying other operators. -/
def expandDefinitions (tm : cvc5.TermManager) (definitions : Array ParsedDefinition)
    (root : cvc5.Term) : cvc5.Env cvc5.Term := do
  if definitions.isEmpty then return root
  return (← expand tm definitions root |>.run {}).1

/-- cvc5 stores each define-fun as `symbol = body`, using a lambda for parameters. -/
def readDefinition (equation : cvc5.Term) (source : Source.Ref)
    (query : ParsedQuery) (tm : cvc5.TermManager) (allowQuantifiers : Bool)
    : cvc5.Env ParsedDefinition := do
  unless (← ofExcept equation.getKind) == .EQUAL && equation.getNumChildren == 2 do
    throw (.error "expected a native defining equation")
  let symbol := equation[0]!
  let sort ← ofExcept symbol.getSort
  unless (← ofExcept symbol.getKind) == .CONSTANT &&
      (isValueSort sort query.valueSorts || (← isSupportedFunction sort query.valueSorts)) do
    throw (.unsupported s!"unsupported definition signature: {sort}; expected supported value sorts")
  let value := equation[1]!
  let (parameters, body) ← if (← ofExcept value.getKind) == .LAMBDA then do
      unless value.getNumChildren == 2 && (← ofExcept value[0]!.getKind) == .VARIABLE_LIST do
        throw (.error "expected a native definition lambda")
      pure (value[0]!.getChildren, value[1]!)
    else pure (#[], value)
  let body ← withoutQuantifierHints tm body
  -- Check before expansion as well: even discarded arguments must be supported.
  validateTerm body (knownTerms query) allowQuantifiers parameters query.valueSorts query.arrayConstructors
  let body ← expandDefinitions tm query.definitions body
  validateTerm body query.declarations allowQuantifiers parameters query.valueSorts query.arrayConstructors
  return { symbol, parameters, body, source }

end Smt2Lean.Backend
