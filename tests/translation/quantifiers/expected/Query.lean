import Init

-- Statements

/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (f0 : Int → Prop), ((∀ (x : Int), f0 x) ∧ ∃ (x : Int), ¬f0 x) → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
