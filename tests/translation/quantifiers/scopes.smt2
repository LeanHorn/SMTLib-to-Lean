; Alternating binders, shadowing, native identities, and Bool used as data.
(set-logic UFLIA)
(declare-const x Int)
(declare-const p Bool)
(declare-fun R (Int Int Bool) Bool)
(declare-fun f (Bool Int) Int)
(declare-fun |True| (Bool) Bool)
(assert (forall ((x Int) (b Bool))
  (exists ((y Int)) (and (= y (+ x 1)) (R x y b)))))
(assert (exists ((x Int)) (forall ((y Int)) (R x y p))))
; Restore the outer x after each inner scope, including the global declaration.
(assert (and (= x 7)
  (forall ((x Int)) (and (>= x 0) (exists ((x Int)) (< x 0)) (= x 1)))
  (= x 8)))
; cvc5 expands let. The saved outer variable must survive inner binders named x.
(assert (forall ((x Int)) (let ((outer x))
  (and (exists ((x Int)) (R outer x p))
       (exists ((x Bool)) (R outer 0 x))
       (R outer x p)))))
(assert (and
  (forall ((|True| Bool) (|a b| Int))
    (exists ((p Bool)) (R |a b| (f (and |True| p) x) (not |True|))))
  (|True| p)))
; Keep premise-only and unused variables, including unused existential witnesses.
(assert (and
  (forall ((b Bool) (y Int)) (=> (and b (= y x)) (R x x p)))
  (forall ((unused Int) (flag Bool)) p)
  (exists ((unused Bool) (value Int)) p)))
(assert (= (f (exists ((y Int)) (= y x)) x)
           (f (forall ((y Int)) (R x y p)) 0)))
(assert (and (forall ((z Int)) (R z x p)) (exists ((z Int)) (R z x p))))
; Quantified conditions and shadowing must not capture variables in either branch.
(assert (forall ((p Bool) (x Int))
  (= (ite (exists ((x Int)) (R x x p))
          (ite p x 0) (ite (forall ((p Bool)) p) 1 x)) x)))
(check-sat)
(exit)
