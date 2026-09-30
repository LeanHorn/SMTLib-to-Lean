import cvc5

namespace Smt2Lean.Backend

/-- Only these native annotations are known to leave the formula unchanged. -/
private def validateHints (tm : cvc5.TermManager) (hints : cvc5.Term) : cvc5.Env Unit := do
  unless (← ofExcept hints.getKind) == .INST_PATTERN_LIST do
    throw (.unsupported "expected a quantifier hint list")
  for hint in hints.getChildren do
    let children := hint.getChildren
    let accepted ← match ← ofExcept hint.getKind with
      | .INST_PATTERN => pure (!children.isEmpty)
      | .INST_NO_PATTERN => pure (children.size == 1)
      | .INST_ATTRIBUTE => do
        if children.size != 2 then pure false
        else pure (children[0]! == (← tm.mkString "qid") &&
          (← ofExcept children[1]!.getKind) == .CONSTANT &&
          (← ofExcept children[1]!.getSort).isBoolean)
      | _ => pure false
    unless accepted do
      throw (.unsupported s!"unsupported quantifier hint: {hint}")

private partial def stripHints (tm : cvc5.TermManager) (term : cvc5.Term)
    : StateT (Std.HashMap cvc5.Term cvc5.Term) cvc5.Env cvc5.Term := do
  if let some result := (← get)[term]? then return result
  let kind ← ofExcept term.getKind
  let original := term.getChildren
  let children ← if kind == .FORALL || kind == .EXISTS then do
    unless original.size == 2 || original.size == 3 do
      throw (.unsupported "expected a quantifier body and optional hints")
    if original.size == 3 then validateHints tm original[2]!
    -- Keep the original binders; only the body contributes to the proposition.
    pure #[original[0]!, ← stripHints tm original[1]!]
  else original.mapM (stripHints tm)
  let result ← if children == original then pure term
    else tm.mkTermOfOp (← ofExcept term.getOp) children
  modify (·.insert term result)
  return result

/-- Remove audited solver hints before validation, expansion, and reconstruction.
Preserve native binder identities and shared subterms; never simplify the body. -/
def withoutQuantifierHints (tm : cvc5.TermManager) (term : cvc5.Term) : cvc5.Env cvc5.Term :=
  (stripHints tm term).run' {}

end Smt2Lean.Backend
