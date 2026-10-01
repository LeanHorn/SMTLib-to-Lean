import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
A proper submodel of Int arrays, closed under stores and constant arrays.
The quantified query below distinguishes it from the full function space.
-/

namespace ArrayModel

/-- Functions that become constant above some integer bound. -/
def Carrier := { f : Int → Int // ∃ n v, ∀ i, n ≤ i → f i = v }

def select (a : Carrier) (i : Int) : Int := a.val i

def const (v : Int) : Carrier :=
  ⟨fun _ => v, ⟨0, v, fun _ _ => rfl⟩⟩

def store (a : Carrier) (i v : Int) : Carrier :=
  ⟨fun j => if j = i then v else a.val j, by
    obtain ⟨n, w, h⟩ := a.property
    refine ⟨max n (i + 1), w, ?_⟩
    intro j hj
    have hnj : n ≤ j := by omega
    have hji : j ≠ i := by omega
    simp [hji, h j hnj]⟩

/-- The exact array laws included in each translated interpretation. -/
def Laws (A : Type) (read : A → Int → Int) (write : A → Int → Int → A) : Prop :=
  Nonempty A ∧
  (∀ a i v, read (write a i v) i = v) ∧
  (∀ a i j v, i ≠ j → read (write a i v) j = read a j) ∧
  (∀ a b, (∀ i, read a i = read b i) → a = b)

theorem model_laws : Laws Carrier select store := by
  refine ⟨⟨const 0⟩, ?_, ?_, ?_⟩
  · intro a i v
    simp [select, store]
  · intro a i j v h
    simp [select, store, Ne.symm h]
  · intro a b h
    apply Subtype.ext
    funext i
    exact h i

theorem const_law : ∀ v i, select (const v) i = v := by
  intros
  rfl

/-- SMT: `(forall ((a (Array Int Int))) (exists ((i Int)) (distinct (select a i) i)))`. -/
def MissesIdentity (A : Type) (read : A → Int → Int) : Prop :=
  ∀ a, ∃ i, read a i ≠ i

theorem restricted_model_misses_identity : MissesIdentity Carrier select := by
  intro a
  obtain ⟨n, v, h⟩ := a.property
  refine ⟨max n (v + 1), ?_⟩
  have hn : n ≤ max n (v + 1) := by omega
  have hv : v < max n (v + 1) := by omega
  change a.val (max n (v + 1)) ≠ max n (v + 1)
  rw [h _ hn]
  omega

theorem full_functions_have_identity : ¬ MissesIdentity (Int → Int) (fun a i => a i) := by
  intro h
  obtain ⟨i, hi⟩ := h (fun i => i)
  exact hi rfl

/-- Even adding every constant array does not require the full function space. -/
theorem proper_model_with_constants :
    Laws Carrier select store ∧
    (∀ v i, select (const v) i = v) ∧
    MissesIdentity Carrier select :=
  ⟨model_laws, const_law, restricted_model_misses_identity⟩

end ArrayModel
