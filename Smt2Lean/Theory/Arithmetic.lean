import Smt2Lean.Theory.Helpers
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Smt2Lean.Arithmetic

open Lean Meta Qq

/-- cvc5 may retain signed integer numerals inside Real arithmetic. -/
private def integerLiteral? (term : cvc5.Term) : Option Int := Id.run do
  let mut value := term
  let mut negative := false
  while value.getKind! == .NEG do
    negative := !negative
    value := value[0]!
  if !value.getSort!.isInteger || !value.isIntegerValue then return none
  let result := value.getIntegerValue!
  return some (if negative then -result else result)

/-- Recognize nonzero literals, including unary minus, without rewriting the query. -/
private def nonzeroLiteral (term : cvc5.Term) : Bool := Id.run do
  let mut value := term
  while value.getKind! == .NEG do value := value[0]!
  return (value.isIntegerValue && value.getIntegerValue! != 0) ||
    (value.isRealValue && value.getRationalValue!.num != 0)

private def zeroKey (kind : cvc5.Kind) : String :=
  if kind == .DIVISION then "SMT.realDivZero"
  else if kind == .INTS_DIVISION then "SMT.divZero" else "SMT.modZero"

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
    if (kind == .INTS_DIVISION || kind == .INTS_MODULUS || kind == .DIVISION) &&
        (term.getChildren.extract 1 term.getNumChildren).any (!nonzeroLiteral ·) then
      unless kinds.contains kind do kinds := kinds.push kind
    pending := pending ++ term.getChildren
  -- Stable parameter order regardless of term traversal order.
  kinds := #[cvc5.Kind.INTS_DIVISION, .INTS_MODULUS, .DIVISION].filter kinds.contains
  let declarations ← kinds.mapM fun kind => do
    let stem := if kind == .DIVISION then `realDivZero
      else if kind == .INTS_DIVISION then `divZero else `modZero
    let type := if kind == .DIVISION then q(Real → Real) else q(Int → Int)
    return (← mkFreshUserName stem, type)
  withLocalDeclsDND declarations fun parameters => do
    let mut userNames := {}
    for kind in kinds, parameter in parameters do
      userNames := userNames.insert (zeroKey kind) parameter
    inspect parameters { userNames }

@[smt_sort_reconstruct] def reconstructRealSort : Smt.SortReconstructor := fun sort => do
  if sort.isReal then return some q(Real)
  return none

/-- Lift Int operands to Real without changing their cached Int reconstruction. -/
private def realOperand (term : cvc5.Term) : Smt.ReconstructM Expr := do
  if let some value := integerLiteral? term then
    let literal : Q(Real) ← mkNumeral q(Real) value.natAbs
    return if value < 0 then q(-$literal) else literal
  if term.getSort!.isInteger then
    let value : Q(Int) ← Smt.Reconstruct.reconstructTerm term
    return q(($value : Real))
  Smt.Reconstruct.reconstructTerm term

/-- Formula reconstruction needs only Mathlib's Real operations, not solver proof rules. -/
private def reconstructReal : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  if kind == .TO_REAL then return ← realOperand term[0]!
  if kind == .TO_INTEGER || kind == .IS_INTEGER then
    let value : Q(Real) ← realOperand term[0]!
    return if kind == .TO_INTEGER then q(Int.floor $value)
      else q($value = (Int.floor $value : Real))
  if kind == .CONST_RATIONAL then
    let value ← ofExcept term.getRationalValue
    let numerator : Q(Real) ← mkNumeral q(Real) value.num.natAbs
    let numerator : Q(Real) := if value.num < 0 then q(-$numerator) else numerator
    if value.den == 1 then return numerator
    let denominator : Q(Real) ← mkNumeral q(Real) value.den
    return q($numerator / $denominator)
  unless #[cvc5.Kind.NEG, .ABS, .ADD, .SUB, .MULT, .DIVISION, .LEQ, .LT, .GEQ, .GT].contains kind do
    return none
  let some first := term.getChildren[0]? | return none
  unless term.getSort!.isReal || term.getChildren.any (·.getSort!.isReal) do return none
  let x : Q(Real) ← realOperand first
  match kind with
  | .NEG => return q(-$x)
  | .ABS => return q(|$x|)
  | .ADD | .SUB | .MULT | .DIVISION =>
    let mut value := x
    for child in term.getChildren[1:] do
      let y : Q(Real) ← realOperand child
      value ← match kind with
        | .ADD => pure q($value + $y)
        | .SUB => pure q($value - $y)
        | .MULT => pure q($value * $y)
        | _ =>
          if nonzeroLiteral child then pure q($value / $y)
          else do
            let some zero := (← read).userNames[zeroKey kind]?
              | throwError "missing interpretation for Real division at zero"
            pure <| mkApp3 (mkConst (← Helpers.realDiv)) zero value y
    return value
  | .LEQ | .LT | .GEQ | .GT =>
    let y : Q(Real) ← realOperand term[1]!
    return match kind with
      | .LEQ => q($x ≤ $y)
      | .LT => q($x < $y)
      | .GEQ => q($x ≥ $y)
      | _ => q($x > $y)
  | _ => return none

/-- Exact integer/Real arithmetic, with explicit interpretations at zero. -/
def reconstruct : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  unless kind == .INTS_DIVISION || kind == .INTS_MODULUS do return ← reconstructReal term
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
