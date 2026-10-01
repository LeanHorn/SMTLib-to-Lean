import Smt2Lean.Theory.Helpers

namespace Smt2Lean.BitVec

open Lean Meta Qq

@[smt_sort_reconstruct] def reconstructSort : Smt.SortReconstructor := fun sort => do
  unless sort.isBitVector do return none
  let width : Nat := (← ofExcept sort.getBitVectorSize).toNat
  return q(BitVec $width)

/-- Indexed width changes and concatenation; native parsing checks the indices. -/
private def reconstructWidthChange : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  unless #[cvc5.Kind.BITVECTOR_CONCAT, .BITVECTOR_EXTRACT, .BITVECTOR_REPEAT,
      .BITVECTOR_ZERO_EXTEND, .BITVECTOR_SIGN_EXTEND].contains kind do return none
  let width : Q(Nat) ← pure <| toExpr term[0]!.getSort!.getBitVectorSize!.toNat
  let x : Q(BitVec $width) ← Smt.Reconstruct.reconstructTerm term[0]!
  if kind == .BITVECTOR_CONCAT then
    let mut value : Expr := x
    for child in term.getChildren[1:] do
      value ← mkAppM ``BitVec.append #[value, ← Smt.Reconstruct.reconstructTerm child]
    return value
  let index : Q(Nat) ← pure <| toExpr term.getOp![0]!.getIntegerValue!.toNat
  match kind with
  | .BITVECTOR_EXTRACT =>
    let lo : Q(Nat) ← pure <| toExpr term.getOp![1]!.getIntegerValue!.toNat
    return q(BitVec.extractLsb $index $lo $x)
  | .BITVECTOR_REPEAT => return q(BitVec.replicate $index $x)
  | _ =>
    -- SMT gives the added bits; Lean expects the final width, w + index.
    let resultWidth : Q(Nat) ← pure <| toExpr term.getSort!.getBitVectorSize!.toNat
    if kind == .BITVECTOR_ZERO_EXTEND then return q(BitVec.zeroExtend $resultWidth $x)
    return q(BitVec.signExtend $resultWidth $x)

/-- Fixed-width formulas using Lean core. Only the audited operators are enabled. -/
def reconstruct : Smt.TermReconstructor := fun term => do
  if let some value ← reconstructWidthChange term then return value
  let kind ← ofExcept term.getKind
  if kind == .CONST_BITVECTOR then
    let width : Q(Nat) ← pure <| toExpr term.getSort!.getBitVectorSize!.toNat
    let some value := (← ofExcept (term.getBitVectorValue 10)).toNat?
      | throwError "invalid native bitvector numeral"
    return ← mkNumeral q(BitVec $width) value
  if kind == .INT_TO_BITVECTOR then
    let width : Q(Nat) ← pure <| toExpr term.getSort!.getBitVectorSize!.toNat
    let value : Q(Int) ← Smt.Reconstruct.reconstructTerm term[0]!
    return q(BitVec.ofInt $width $value)
  unless #[cvc5.Kind.BITVECTOR_NEG, .BITVECTOR_NOT, .BITVECTOR_ADD, .BITVECTOR_SUB,
      .BITVECTOR_MULT, .BITVECTOR_AND, .BITVECTOR_OR, .BITVECTOR_XOR, .BITVECTOR_NAND,
      .BITVECTOR_NOR, .BITVECTOR_XNOR, .BITVECTOR_COMP, .BITVECTOR_ULT, .BITVECTOR_ULE,
      .BITVECTOR_UGT, .BITVECTOR_UGE, .BITVECTOR_SLT, .BITVECTOR_SLE,
      .BITVECTOR_SGT, .BITVECTOR_SGE, .BITVECTOR_SHL, .BITVECTOR_LSHR, .BITVECTOR_ASHR,
      .BITVECTOR_UDIV, .BITVECTOR_UREM, .BITVECTOR_SDIV, .BITVECTOR_SREM, .BITVECTOR_SMOD,
      .BITVECTOR_UBV_TO_INT, .BITVECTOR_SBV_TO_INT, .BITVECTOR_NEGO,
      .BITVECTOR_UADDO, .BITVECTOR_SADDO, .BITVECTOR_UMULO, .BITVECTOR_SMULO,
      .BITVECTOR_ROTATE_LEFT, .BITVECTOR_ROTATE_RIGHT].contains kind do return none
  let width : Q(Nat) ← pure <| toExpr term[0]!.getSort!.getBitVectorSize!.toNat
  let x : Q(BitVec $width) ← Smt.Reconstruct.reconstructTerm term[0]!
  if kind == .BITVECTOR_NEG then return q(-$x)
  if kind == .BITVECTOR_NOT then return q(~~~$x)
  if kind == .BITVECTOR_UBV_TO_INT then return q((BitVec.toNat $x : Int))
  if kind == .BITVECTOR_SBV_TO_INT then return q(BitVec.toInt $x)
  if kind == .BITVECTOR_NEGO then return q(BitVec.negOverflow $x = true)
  if kind == .BITVECTOR_ROTATE_LEFT || kind == .BITVECTOR_ROTATE_RIGHT then
    let amount : Q(Nat) ← pure <| toExpr term.getOp![0]!.getIntegerValue!.toNat
    if kind == .BITVECTOR_ROTATE_LEFT then return q(BitVec.rotateLeft $x $amount)
    return q(BitVec.rotateRight $x $amount)
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
  -- SMT fixes division by zero; ordinary Lean BV division returns zero instead.
  | .BITVECTOR_UDIV => return q(BitVec.smtUDiv $x $y)
  | .BITVECTOR_UREM => return q($x % $y)
  | .BITVECTOR_SDIV => return q(BitVec.smtSDiv $x $y)
  | .BITVECTOR_SREM => return q(BitVec.srem $x $y)
  | .BITVECTOR_SMOD => return q(BitVec.smod $x $y)
  | .BITVECTOR_UADDO => return q(BitVec.uaddOverflow $x $y = true)
  | .BITVECTOR_SADDO => return q(BitVec.saddOverflow $x $y = true)
  | .BITVECTOR_UMULO => return q(BitVec.umulOverflow $x $y = true)
  | .BITVECTOR_SMULO => return q(BitVec.smulOverflow $x $y = true)
  | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP
  | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR =>
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
