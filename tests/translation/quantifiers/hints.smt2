; Each annotated assertion is followed by its unannotated equivalent.
(set-logic ALL)
(declare-const x Int)
(declare-fun P (Int) Bool)
(declare-fun R (Int Bool) Bool)
(define-fun lifted ((n Int)) Bool
  (forall ((b Bool)) (! (R n b) :pattern ((R n b)) :qid helper)))

; Multiple triggers and an excluded trigger. Unsupported exponentiation occurs only in a discarded hint.
(assert (forall ((x Int))
  (! (P x) :pattern ((P x)) :pattern ((P (+ x 1)))
    :no-pattern (P (^ x 2)) :qid |rule :named id|)))
(assert (forall ((x Int)) (P x)))

; Alternating quantifiers, shadowing, and a qid that matches a global name.
(assert (forall ((x Int))
  (! (let ((outer x))
       (exists ((x Int) (b Bool))
         (! (and (= outer x) (R x b)) :pattern ((R x b)) :qid witness)))
     :pattern ((P x)) :qid x)))
(assert (forall ((x Int)) (let ((outer x))
  (exists ((x Int) (b Bool)) (and (= outer x) (R x b))))))

; Shared quantified terms and a free global inside the body.
(assert (let ((q (forall ((b Bool)) (! (R x b) :pattern ((R x b)) :qid bool))))
  (and q q)))
(assert (let ((q (forall ((b Bool)) (R x b)))) (and q q)))

; Hints inside a definition disappear before substitution.
(assert (forall ((n Int)) (lifted n)))
(assert (forall ((n Int)) (forall ((b Bool)) (R n b))))

; Empty patterns and a named, reusable quantified assertion.
(assert (! (forall ((x Int)) (! (P x) :pattern () :qid empty)) :named allP))
(assert allP)
(check-sat)
