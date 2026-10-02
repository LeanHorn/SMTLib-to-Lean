import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/translation/quantifiers/quantified.smt2":6:1-6:12 (check-sat, command 5)
-- Source: "tests/translation/quantifiers/quantified.smt2":4:1-4:34 (assertion 1, command 3)
-- Source: "tests/translation/quantifiers/quantified.smt2":5:1-5:40 (assertion 2, command 4)
/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (f0 : Int → Prop), ((∀ (x : Int), f0 x) ∧ ∃ (x : Int), ¬f0 x) → False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
