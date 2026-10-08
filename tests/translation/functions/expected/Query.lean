import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/translation/functions/congruence.smt2":6:1-6:17 (assertion 1, command 5)
def Refutation_1.Assertion001
    (x1 : Int)
    (x2 : Int) : Prop :=
  x1 = x2

-- Source: "tests/translation/functions/congruence.smt2":7:1-7:31 (assertion 2, command 6)
def Refutation_1.Assertion002
    (f0 : Int → Int)
    (x1 : Int)
    (x2 : Int) : Prop :=
  ¬f0 x1 = f0 x2

-- Source: "tests/translation/functions/congruence.smt2":8:1-8:12 (check-sat, command 7)
/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (f0 : Int → Int),
  ∀ (x1 x2 : Int),
  ((Refutation_1.Assertion001 x1 x2) ∧
  Refutation_1.Assertion002 f0 x1 x2) →
  False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
