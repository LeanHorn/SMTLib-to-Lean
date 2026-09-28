; Equal inputs cannot give different outputs for the same function.
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
(exit)
