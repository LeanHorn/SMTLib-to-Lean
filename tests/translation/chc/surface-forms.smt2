; Equivalent Horn syntax; relation identities and source assertions survive normalization.
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-const done Bool)
; A negated conjunction becomes separate positive premises.
(assert (forall ((x Int)) (or (not (and (P x) (> x 0))) (Q x))))
; Nested disjunctions may contain theory literals alongside one positive relation.
(assert (forall ((x Int)) (or (not (P x)) (or (< x 0) (Q x)))))
(assert (forall ((x Int)) (=> (P x) (or (not (> x 0)) (Q x)))))
; Each conjunct retains the original assertion number and enclosing binders.
(assert (and (P 0) (forall ((x Int))
  (and (or (not (P x)) (Q x)) (=> (Q x) (>= x 0))))))
; Split under shadowed quantifiers without capturing the outer x.
(assert (forall ((x Int)) (let ((outer x)) (forall ((x Int))
  (and (or (not (P outer)) (Q x)) (or (not (Q x)) (= outer x)))))))
; Pure theory assertions and true heads are constraints, not relation declarations.
(assert (forall ((x Int)) (or (< x 0) (>= x 0))))
(assert (=> done true))
(assert (not done))
(assert (forall ((x Int)) (or (not (and (P x) (Q x))) false)))
(assert (forall ((x Int)) (= x x)))
(check-sat)
