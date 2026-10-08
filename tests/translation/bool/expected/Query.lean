import Init

set_option maxRecDepth 4096

-- Statements

-- Source: "tests/translation/bool/contradiction.smt2":3:1-3:11 (assertion 1, command 3)
def Refutation_1.Assertion001
    (p0 : Prop) : Prop :=
  p0

-- Source: "tests/translation/bool/contradiction.smt2":4:1-4:17 (assertion 2, command 4)
def Refutation_1.Assertion002
    (p0 : Prop) : Prop :=
  ¬p0

-- Source: "tests/translation/bool/contradiction.smt2":5:1-5:12 (check-sat, command 5)
/-- No interpretation satisfies all assertions of the SMT query. -/
def Refutation : Prop :=
  ∀ (p0 : Prop),
  ((Refutation_1.Assertion001 p0) ∧
  Refutation_1.Assertion002 p0) →
  False

-- Proofs

-- Unfinished proof: replace sorry to establish the query's refutation.
theorem refutation : Refutation := by
  sorry
