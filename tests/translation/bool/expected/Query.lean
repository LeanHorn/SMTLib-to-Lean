import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/translation/bool/contradiction.smt2":5:1-5:12 (check-sat, command 5)
-- Source: "tests/translation/bool/contradiction.smt2":3:1-3:11 (assertion 1, command 3)
-- Source: "tests/translation/bool/contradiction.smt2":4:1-4:17 (assertion 2, command 4)
/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (p0 : Prop), p0 ∧ ¬p0 → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
