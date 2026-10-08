import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/chc/lh_sum_rec.smt2":21:1-22:64 (clause 1, command 4)
def Problem_1.Clause001
    (r0 : Int → Prop) : Prop :=
  ∀ (n : Int),
  ∀ (cond : Prop),
  ∀ (VV : Int),
  (cond = (n ≤ (0 : Int))) →
  (cond) →
  (VV = (0 : Int)) →
  r0 VV

-- Source: "tests/chc/lh_sum_rec.smt2":23:1-24:99 (clause 2, command 5)
def Problem_1.Clause002
    (r0 : Int → Prop) : Prop :=
  ∀ (n : Int),
  ∀ (cond : Prop),
  ∀ (n1 : Int),
  ∀ (t1 : Int),
  ∀ (v : Int),
  (cond = (n ≤ (0 : Int))) →
  (¬cond) →
  (n1 = n - (1 : Int)) →
  (r0 t1) →
  (v = n + t1) →
  r0 v

-- Source: "tests/chc/lh_sum_rec.smt2":25:1-26:87 (clause 3, command 6)
def Problem_1.Clause003
    (r0 : Int → Prop) : Prop :=
  ∀ (r : Int),
  ∀ (ok1 : Prop),
  ∀ (v : Prop),
  (r0 r) →
  (ok1 = ((0 : Int) ≤ r)) →
  (v = ((0 : Int) ≤ r)) →
  (v = ok1) →
  (¬v) →
  False

-- Source: "tests/chc/lh_sum_rec.smt2":28:1-28:12 (check-sat, command 7)
/-- There are relation interpretations satisfying every Horn clause. -/
def Problem : Prop :=
  ∃ (r0 : Int → Prop),
  (Problem_1.Clause001 r0) ∧
  (Problem_1.Clause002 r0) ∧
  Problem_1.Clause003 r0

-- Proofs

-- Unfinished proof: replace sorry to establish the existence of satisfying relations.
theorem problem : Problem := by
  sorry
