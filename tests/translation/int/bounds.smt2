; Contradictory bounds: the same integer cannot be nonnegative and negative.
(set-logic QF_LIA)
(declare-const x Int)
(assert (>= x 0))
(assert (< x 0))
(check-sat)
(exit)
