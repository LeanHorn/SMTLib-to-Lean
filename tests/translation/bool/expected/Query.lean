import Init

-- Statements

/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (p0 : Prop), p0 ∧ ¬p0 → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
