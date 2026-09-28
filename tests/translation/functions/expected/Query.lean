import Init

-- Statements

/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (f0 : Int → Int) (x1 x2 : Int), x1 = x2 ∧ ¬f0 x1 = f0 x2 → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
