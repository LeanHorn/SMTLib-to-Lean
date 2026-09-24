/-!
# Smt2Lean prelude

Definitions the generated Lean files rely on. Everything here is Mathlib-free.
SMT-LIB arrays are total functions, so `(Array I E)` is `I → E`; sets `(Array T Bool)`
become `T → Prop`.
-/
namespace Smt2Lean
open Classical

/-- SMT-LIB `(Array ι ε)`. -/
abbrev SmtArray (ι ε : Type) := ι → ε

/-- `((as const (Array ι ε)) v)`. -/
def SmtArray.const {ι ε : Type} (v : ε) : SmtArray ι ε := fun _ => v

/-- `(store a i v)`. -/
noncomputable def SmtArray.store {ι ε : Type} (a : SmtArray ι ε) (i : ι) (v : ε) : SmtArray ι ε :=
  fun j => if j = i then v else a j

/-- z3's `((_ map f) a)` for unary `f`. -/
def SmtArray.map1 {ι α β : Type} (f : α → β) (a : SmtArray ι α) : SmtArray ι β :=
  fun i => f (a i)

/-- z3's `((_ map f) a b)` for binary `f`, e.g. `(_ map or)` for set union. -/
def SmtArray.map2 {ι α β γ : Type} (f : α → β → γ) (a : SmtArray ι α) (b : SmtArray ι β) :
    SmtArray ι γ :=
  fun i => f (a i) (b i)

/-- SMT-LIB `abs` on integers. -/
def smtAbs (x : Int) : Int := if x < 0 then -x else x

/-- `(ite b 1 0)` on a proposition. -/
noncomputable def boolToInt (p : Prop) : Int := if p then 1 else 0

/-- `str.len`, counted in characters. -/
def strLen (s : String) : Int := s.length

/-- `str.substr s i n`: the empty string when out of range, as in SMT-LIB. -/
def strSubstr (s : String) (i n : Int) : String :=
  if i < 0 ∨ n < 0 ∨ i ≥ s.length then "" else String.ofList ((s.toList.drop i.toNat).take n.toNat)

end Smt2Lean
