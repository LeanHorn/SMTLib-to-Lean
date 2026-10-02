import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/translation/int/bounds.smt2":6:1-6:12 (check-sat, command 5)
-- Source: "tests/translation/int/bounds.smt2":4:1-4:18 (assertion 1, command 3)
-- Source: "tests/translation/int/bounds.smt2":5:1-5:17 (assertion 2, command 4)
/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (x0 : Int), x0 ≥ (0 : Int) ∧ x0 < (0 : Int) → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
