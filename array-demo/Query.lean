import Init

-- Statements

def SMT.arrayLaws (I : Type) (E : Type) (A : Type) (select : A → I → E) (store : A → I → E → A) : Prop :=
  Nonempty A ∧
    (∀ (a : A) (i : I) (v : E), select (store a i v) i = v) ∧
      (∀ (a : A) (i j : I) (v : E), i ≠ j → select (store a i v) j = select a j) ∧
        ∀ (a b : A), (∀ (i : I), select a i = select b i) → a = b

def SMT.distinct2.{u} {α : Sort u} (x0 : α) (x1 : α) : Prop :=
  x0 ≠ x1

-- Source: "tests/translation/arrays/operations.smt2":15:1-15:12 (check-sat, command 15)
-- Source: "tests/translation/arrays/operations.smt2":10:1-10:42 (assertion 1, command 10)
-- Source: "tests/translation/arrays/operations.smt2":11:1-11:71 (assertion 2, command 11)
-- Source: "tests/translation/arrays/operations.smt2":12:1-12:45 (assertion 3, command 12)
-- Source: "tests/translation/arrays/operations.smt2":13:1-13:24 (assertion 4, command 13)
-- Source: "tests/translation/arrays/operations.smt2":14:1-14:58 (assertion 5, command 14)
/-- No interpretation satisfies all assertions of the SMT query. -/
noncomputable def Refutation : Prop := by
  classical
  exact
    ∀ (Array : Type) (select : Array → Int → Int) (store : Array → Int → Int → Array) (x0 x1 : Array) (x2 x3 : Int)
      (p4 : Prop) (f5 : Array → Array),
      SMT.arrayLaws Int Int Array select store →
        (select (store x0 x2 (x2 + (1 : Int))) x2 = x2 + (1 : Int) ∧
            (SMT.distinct2 x2 x3 → select (store x0 x2 (7 : Int)) x3 = select x0 x3) ∧
              ((if p4 then f5 x0 else x1) = if p4 then f5 x0 else x1) ∧
                SMT.distinct2 x0 x1 ∧ ∀ (k : Int), select x0 k = select x1 k) →
          False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
