import Init

-- Statements

/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (x0 : Int), x0 ≥ (0 : Int) ∧ x0 < (0 : Int) → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
