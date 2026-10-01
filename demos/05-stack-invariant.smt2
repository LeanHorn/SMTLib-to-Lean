; Is there a model proving stack operations preserve a consistent height? Expected: sat.
; Showcase: recursive Horn clauses, datatypes, testers, match, and integer guards.
; A model is Reach(s, n) iff n is the structural length of s.
(set-logic HORN)
(declare-datatype Stack ((empty) (frame (value Int) (rest Stack))))
(declare-fun Reach (Stack Int) Bool)

; Initial state.
(assert (Reach empty 0))

; Push a value.
(assert (forall ((s Stack) (n Int) (v Int))
  (=> (Reach s n) (Reach (frame v s) (+ n 1)))))

; Pop only a nonempty stack; match extracts the remaining stack.
(assert (forall ((s Stack) (n Int))
  (=> (and (Reach s n) ((_ is frame) s))
      (Reach (match s ((empty empty) ((frame v tail) tail))) (- n 1)))))

; A reachable height must be nonnegative and agree with the stack's shape.
(assert (forall ((s Stack) (n Int))
  (=> (and (Reach s n)
           (or (< n 0)
               (match s ((empty (distinct n 0)) ((frame v tail) (<= n 0))))))
      false)))
(check-sat)
