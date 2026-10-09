import Smt2Lean.Backend.Validate
import Smt2Lean.Backend.Hints
import Smt2Lean.Backend.SourceLets

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

/-- Unfold only the outer call, retaining nested calls and source lets. -/
def unfoldDefinition (tm : cvc5.TermManager) (definitions : Array ParsedDefinition)
    (term : cvc5.Term) : cvc5.Env (Option cvc5.Term) := do
  let head := if term.getKind! == .APPLY_UF then term[0]! else term
  let some definition := definitions.find? (·.symbol == head) | return none
  let arguments := if term.getKind! == .APPLY_UF then term.getChildren.extract 1 term.getNumChildren else #[]
  return some (← (instantiate tm (definition.sourceBody.getD definition.body)
    definition.parameters arguments).run {}).1

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
  let sourceBody := body
  let body ← SourceLets.erase tm query.sourceLets body
  let body ← expandDefinitions tm query.definitions body
  validateTerm body query.declarations allowQuantifiers parameters query.valueSorts query.arrayConstructors
  return { symbol, parameters, body, sourceBody := some sourceBody, source }

/-- cvc5 attaches a private function-definition hint to recursive equations.
Remove only its exact self-application marker; audit other hints normally. -/
private def recursiveEquation (tm : cvc5.TermManager) (equation : cvc5.Term)
    : cvc5.Env cvc5.Term := do
  let mut equation := equation
  if equation.getKind! == .FORALL && equation.getNumChildren == 3 then
    let body := equation[1]!
    let hints := equation[2]!
    if body.getKind! == .EQUAL && hints.getKind! == .INST_PATTERN_LIST then
      let remaining := hints.getChildren.filter fun hint =>
        !(hint.getKind! == .INST_ATTRIBUTE && hint.getNumChildren == 1 && hint[0]! == body[0]!)
      let children := #[equation[0]!, body]
      let children ← if remaining.isEmpty then pure children else do
        pure (children.push (← tm.mkTerm .INST_PATTERN_LIST remaining))
      equation ← tm.mkTerm .FORALL children
  withoutQuantifierHints tm equation

/-- Register the whole recursive group before checking any body. Keep its equations
as constraints; never put these functions in the abbreviation expansion table. -/
def readRecursiveDefinitions (equations : Array cvc5.Term) (source : Source.Ref)
    (query : ParsedQuery) (tm : cvc5.TermManager) (allowQuantifiers : Bool)
    (arrayConstants : Array cvc5.Term := #[]) : cvc5.Env ParsedQuery := do
  if equations.isEmpty then throw (.error "expected recursive defining equations")
  let equations ← equations.mapM (recursiveEquation tm)
  let mut query := query
  let mut functions := #[]
  for equation in equations do
    let body := if equation.getKind! == .FORALL then equation[1]! else equation
    unless body.getKind! == .EQUAL && body.getNumChildren == 2 do
      throw (.error "expected a recursive defining equality")
    let lhs := body[0]!
    let symbol := if lhs.getKind! == .APPLY_UF then lhs[0]! else lhs
    let sort := symbol.getSort!
    unless symbol.getKind! == .CONSTANT &&
        (isValueSort sort query.valueSorts || (← isSupportedFunction sort query.valueSorts)) do
      throw (.unsupported s!"unsupported recursive signature: {sort}")
    let name ← ofExcept symbol.getSymbol
    if (knownTerms query).any (·.name == name) then
      throw (.unsupported s!"duplicate recursive definition: {name}")
    functions := functions.push symbol
    query := { query with declarations := query.declarations.push { name, term := symbol, source := some source } }
  for symbol in functions, surface in equations do
    validateAssertion surface (knownTerms query) allowQuantifiers query.valueSorts query.arrayConstructors
    let term ← SourceLets.erase tm query.sourceLets surface
    let term ← expandDefinitions tm query.definitions term
    validateAssertion term query.declarations allowQuantifiers query.valueSorts query.arrayConstructors
    query := { query with recursiveDefinitions := query.recursiveDefinitions.push {
      symbol, equation := { term, surface := some surface, source, arrayConstants } } }
  return query

end Smt2Lean.Backend
