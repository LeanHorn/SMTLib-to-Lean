; Definitions stay named; lets keep their source names and simultaneous scope.
(set-logic ALL)
(declare-const x Int)
(define-fun inc ((n Int)) Int (+ n 1))
(define-fun twice ((n Int)) Int (inc (inc n)))
(assert (let ((next (twice x)) (old x)) (= next (+ old 2))))
(assert (forall ((x Int)) (let ((next (inc x))) (> next x))))
(check-sat)
