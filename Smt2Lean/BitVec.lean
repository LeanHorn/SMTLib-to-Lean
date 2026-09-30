import Smt2Lean.Helpers

namespace Smt2Lean.BitVec

open Lean Meta Qq

@[smt_sort_reconstruct] def reconstructSort : Smt.SortReconstructor := fun sort => do
  unless sort.isBitVector do return none
  let width : Nat := (← ofExcept sort.getBitVectorSize).toNat
  return q(BitVec $width)

/-- Fixed-width formulas using Lean core. Only the audited operators are enabled. -/
def reconstruct : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  if kind == .CONST_BITVECTOR then
    let width : Q(Nat) ← pure <| toExpr term.getSort!.getBitVectorSize!.toNat
    let some value := (← ofExcept (term.getBitVectorValue 10)).toNat?
      | throwError "invalid native bitvector numeral"
    return ← mkNumeral q(BitVec $width) value
  unless #[cvc5.Kind.BITVECTOR_NEG, .BITVECTOR_NOT, .BITVECTOR_ADD, .BITVECTOR_SUB,
      .BITVECTOR_MULT, .BITVECTOR_AND, .BITVECTOR_OR, .BITVECTOR_XOR, .BITVECTOR_NAND,
      .BITVECTOR_NOR, .BITVECTOR_XNOR, .BITVECTOR_COMP, .BITVECTOR_ULT, .BITVECTOR_ULE,
      .BITVECTOR_UGT, .BITVECTOR_UGE, .BITVECTOR_SLT, .BITVECTOR_SLE,
      .BITVECTOR_SGT, .BITVECTOR_SGE].contains kind do return none
  let width : Q(Nat) ← pure <| toExpr term[0]!.getSort!.getBitVectorSize!.toNat
  let x : Q(BitVec $width) ← Smt.Reconstruct.reconstructTerm term[0]!
  if kind == .BITVECTOR_NEG then return q(-$x)
  if kind == .BITVECTOR_NOT then return q(~~~$x)
  if #[cvc5.Kind.BITVECTOR_ADD, .BITVECTOR_MULT, .BITVECTOR_AND,
      .BITVECTOR_OR, .BITVECTOR_XOR].contains kind then
    let mut value : Q(BitVec $width) := x
    for child in term.getChildren[1:] do
      let y : Q(BitVec $width) ← Smt.Reconstruct.reconstructTerm child
      value := match kind with
        | .BITVECTOR_ADD => q($value + $y)
        | .BITVECTOR_MULT => q($value * $y)
        | .BITVECTOR_AND => q($value &&& $y)
        | .BITVECTOR_OR => q($value ||| $y)
        | _ => q($value ^^^ $y)
    return value
  let y : Q(BitVec $width) ← Smt.Reconstruct.reconstructTerm term[1]!
  match kind with
  | .BITVECTOR_SUB => return q($x - $y)
  | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP =>
    return mkApp3 (mkConst (← Helpers.bitvec kind)) width x y
  | .BITVECTOR_ULT => return q($x < $y)
  | .BITVECTOR_ULE => return q($x ≤ $y)
  | .BITVECTOR_UGT => return q($x > $y)
  | .BITVECTOR_UGE => return q($x ≥ $y)
  | .BITVECTOR_SLT => return q(BitVec.slt $x $y = true)
  | .BITVECTOR_SLE => return q(BitVec.sle $x $y = true)
  | .BITVECTOR_SGT => return q(BitVec.slt $y $x = true)
  | .BITVECTOR_SGE => return q(BitVec.sle $y $x = true)
  | _ => return none

end Smt2Lean.BitVec
