; Every integer satisfies P, but some integer does not.
(set-logic UFLIA)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P x)))
(assert (exists ((x Int)) (not (P x))))
(check-sat)
(exit)
