import Smt2Lean.Helpers

namespace Smt2Lean.Arithmetic

open Lean Meta Qq

/-- Recognize nonzero literals, including unary minus, without rewriting the query. -/
private def nonzeroLiteral (term : cvc5.Term) : Bool := Id.run do
  let mut value := term
  while value.getKind! == .NEG do value := value[0]!
  return value.isIntegerValue && value.getIntegerValue! != 0

private def zeroKey (kind : cvc5.Kind) : String :=
  if kind == .INTS_DIVISION then "SMT.divZero" else "SMT.modZero"

/-- One interpretation per zero-case operation, shared across all assertions and binders.
Source declarations use termCache by native identity; userNames holds only these internal bindings. -/
def withZeroCases [Inhabited α] (terms : Array cvc5.Term)
    (inspect : Array Expr → Smt.Reconstruct.Context → MetaM α) : MetaM α := do
  let mut pending := terms
  let mut visited : Std.HashSet cvc5.Term := {}
  let mut kinds : Array cvc5.Kind := #[]
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    let kind := term.getKind!
    if (kind == .INTS_DIVISION || kind == .INTS_MODULUS) &&
        (term.getChildren.extract 1 term.getNumChildren).any (!nonzeroLiteral ·) then
      unless kinds.contains kind do kinds := kinds.push kind
    pending := pending ++ term.getChildren
  -- Stable parameter order regardless of term traversal order.
  kinds := #[cvc5.Kind.INTS_DIVISION, .INTS_MODULUS].filter kinds.contains
  let declarations ← kinds.mapM fun kind => do
    let stem := if kind == .INTS_DIVISION then `divZero else `modZero
    return (← mkFreshUserName stem, q(Int → Int))
  withLocalDeclsDND declarations fun parameters => do
    let mut userNames := {}
    for kind in kinds, parameter in parameters do
      userNames := userNames.insert (zeroKey kind) parameter
    inspect parameters { userNames }

/-- Euclidean division away from zero, with explicit interpretations at zero. -/
def reconstruct : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  unless kind == .INTS_DIVISION || kind == .INTS_MODULUS do return none
  let mut value : Q(Int) ← Smt.Reconstruct.reconstructTerm term[0]!
  for divisor in term.getChildren[1:] do
    let y : Q(Int) ← Smt.Reconstruct.reconstructTerm divisor
    if nonzeroLiteral divisor then
      value := if kind == .INTS_DIVISION then q($value / $y) else q($value % $y)
    else
      let some zero := (← read).userNames[zeroKey kind]?
        | throwError "missing interpretation for {kind} at zero"
      let helper ← if kind == .INTS_DIVISION then Helpers.intDiv else Helpers.intMod
      value := mkApp3 (mkConst helper) zero value y
  return value

end Smt2Lean.Arithmetic
