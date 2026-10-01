import Smt.Reconstruct.Builtin
import Mathlib.Data.Real.Basic

namespace Smt2Lean.Helpers

open Lean Meta Qq

-- Keep printed types usable in Init-only output after importing Mathlib's notation.
@[delab app.Nat, delab app.Int, delab app.Real] private def printScalar : Lean.PrettyPrinter.Delaborator.Delab :=
  Lean.PrettyPrinter.Delaborator.delabConst

/-- Names reserved for the operator definitions copied into generated files. -/
def isHelper (name : Name) : Bool :=
  #[`SMT.xor, `SMT.intDiv, `SMT.intMod, `SMT.realDiv, `SMT.arrayLaws, `SMT.constArrayLaw,
    `SMT.bvnand, `SMT.bvnor, `SMT.bvxnor, `SMT.bvcomp,
    `SMT.bvshl, `SMT.bvlshr, `SMT.bvashr].contains name || match name with
    | .str `SMT suffix => suffix.startsWith "distinct" &&
        (suffix.drop 8).toString.toNat?.isSome
    | _ => false

private def define (name : Name) (levels : List Name) (value : Expr) : MetaM Name := do
  unless (← getEnv).contains name do
    let declaration : Declaration := .defnDecl {
      name, levelParams := levels, type := ← inferType value, value
      hints := .abbrev, safety := .safe
    }
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore 0 1000 declaration none
    setEnv env
  return name

def xor : MetaM Name :=
  define `SMT.xor [] q(fun (p q : Prop) => (p ∧ ¬q) ∨ (¬p ∧ q))

/-- An arbitrary nonempty array carrier satisfying the three ArraysEx laws. -/
def arrayLaws : MetaM Name :=
  define `SMT.arrayLaws [] q(fun (I E A : Type) (select : A → I → E)
    (store : A → I → E → A) =>
      Nonempty A ∧
      (∀ a i v, select (store a i v) i = v) ∧
      (∀ a i j v, i ≠ j → select (store a i v) j = select a j) ∧
      (∀ a b, (∀ i, select a i = select b i) → a = b))

/-- Constant arrays extend a model only for array sorts using the const constructor. -/
def constArrayLaw : MetaM Name :=
  define `SMT.constArrayLaw [] q(fun (I E A : Type) (select : A → I → E)
    (const : E → A) => ∀ v i, select (const v) i = v)

/-- Keep bitvector operators named in generated statements. -/
def bitvec (kind : cvc5.Kind) : MetaM Name := do
  match kind with
  | .BITVECTOR_NAND => define `SMT.bvnand [] q(fun {w : Nat} (x y : BitVec w) => ~~~(x &&& y))
  | .BITVECTOR_NOR => define `SMT.bvnor [] q(fun {w : Nat} (x y : BitVec w) => ~~~(x ||| y))
  | .BITVECTOR_XNOR => define `SMT.bvxnor [] q(fun {w : Nat} (x y : BitVec w) => ~~~(x ^^^ y))
  | .BITVECTOR_COMP => define `SMT.bvcomp [] q(fun {w : Nat} (x y : BitVec w) => BitVec.ofBool (x == y))
  -- All shifts saturate at the width. Bounding the amount avoids huge intermediates.
  | .BITVECTOR_SHL => define `SMT.bvshl [] q(fun {w : Nat} (x y : BitVec w) => x <<< min y.toNat w)
  | .BITVECTOR_LSHR => define `SMT.bvlshr [] q(fun {w : Nat} (x y : BitVec w) => x >>> min y.toNat w)
  | .BITVECTOR_ASHR => define `SMT.bvashr [] q(fun {w : Nat} (x y : BitVec w) => x.sshiftRight (min y.toNat w))
  | _ => throwError "unsupported bitvector helper: {kind}"

/-- SMT integer division has an unconstrained, input-dependent result at zero. -/
def intDiv : MetaM Name :=
  define `SMT.intDiv [] q(fun (zero : Int → Int) (x y : Int) =>
    if y = 0 then zero x else x / y)

/-- Modulo has its own zero-case interpretation, independent of division. -/
def intMod : MetaM Name :=
  define `SMT.intMod [] q(fun (zero : Int → Int) (x y : Int) =>
    if y = 0 then zero x else x % y)

/-- Real division also leaves the result at zero unconstrained. -/
def realDiv : MetaM Name :=
  define `SMT.realDiv [] q(fun (zero : Real → Real) (x y : Real) =>
    if y = 0 then zero x else x / y)

/-- One polymorphic helper per arity, sharing lean-smt's pairwise encoding. -/
def distinct (arity : Nat) : MetaM Name := do
  let name := Name.str `SMT s!"distinct{arity}"
  if (← getEnv).contains name then return name
  let u := Level.param `u
  withLocalDecl `α .implicit (.sort u) fun α => do
    withLocalDeclsDND (Array.ofFn (n := arity) fun i => (Name.mkSimple s!"x{i.val}", α)) fun xs => do
      let body := Smt.Reconstruct.Builtin.buildDistinct u α xs.toList
      define name [`u] (← mkLambdaFVars (#[α] ++ xs) body)

end Smt2Lean.Helpers
