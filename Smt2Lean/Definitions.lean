import cvc5
import Smt2Lean.Source

namespace Smt2Lean.Backend

/-- A checked definition, with earlier definitions already expanded in its body. -/
structure ParsedDefinition where
  symbol : cvc5.Term
  parameters : Array cvc5.Term
  body : cvc5.Term
  source : Source.Ref

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
  let result ← if kind == .FORALL || kind == .EXISTS then do
    let old := term[0]!.getChildren
    let fresh ← old.mapM fun v => do tm.mkVar (← ofExcept v.getSort) (← ofExcept v.getSymbol)
    let body ← instantiate tm term[1]! (old ++ variables) (fresh ++ values)
    tm.mkTerm kind #[← tm.mkTerm .VARIABLE_LIST fresh, body]
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

/--
cvc5 prints aliases with their bodies already resolved. A supported body is Bool,
Int, or a formal sort parameter. Tokenize this small canonical header, respecting
quoted names; cvc5 still handles alias syntax, arity, scope, and substitution.
-/
def validateSortAlias (command : cvc5.Command) : cvc5.Env Unit := do
  let mut tokens : Array String := #[]
  let mut token := ""
  let mut quoted := false
  for c in command.toString.toList do
    if c == '|' then quoted := !quoted
    if !quoted && (c.isWhitespace || c == '(' || c == ')') then
      if !token.isEmpty then tokens := tokens.push token
      token := ""
      if c == '(' || c == ')' then tokens := tokens.push (String.singleton c)
    else token := token.push c
  unless token.isEmpty do tokens := tokens.push token
  let some endParams := (tokens.extract 4 tokens.size).findIdx? (· == ")")
    | throw (.unsupported s!"unsupported sort alias: {command}")
  let endParams := endParams + 4
  let body := tokens[endParams + 1]?.getD ""
  unless tokens.size == endParams + 3 && tokens[0]? == some "(" &&
      tokens[1]? == some "define-sort" && tokens[3]? == some "(" &&
      tokens.back? == some ")" &&
      (body == "Bool" || body == "Int" || (tokens.extract 4 endParams).contains body) do
    throw (.unsupported s!"unsupported sort alias: {command}; expected Bool, Int, or a sort parameter")

end Smt2Lean.Backend
