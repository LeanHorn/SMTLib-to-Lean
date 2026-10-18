; Hoice/Eldarica forms: negated existentials, De Morgan, and nested conclusions.
(set-logic HORN)
(set-info :origin "compact regression for benchmark clause forms")
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
; A question-mark name and its printable replacement must remain distinct.
(assert (not (exists ((?x Int) (|smt_?x| Int))
  (and (P ?x) (= ?x |smt_?x|) (< |smt_?x| 0)))))
(assert (forall ((x Int)) (not (and (P x) (not (Q x))))))
; The old x remains in the premise and let, while the new x belongs to the head.
(assert (forall ((x Int)) (let ((?old x))
  (=> (P x) (forall ((x Int))
    (and (Q x) (=> (= ?old x) (P ?old))))))))
(assert (forall ((x Int)) (=> (> x 0)
  (and (P x) (forall ((y Int)) (=> (< y x) (Q y)))))))
(check-sat)
