; All right-hand sides use the outer scope, before any new binding is visible.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const p Bool)

; y receives the outer x: this asserts outer_x = 1.
(assert (let ((x 1) (y x)) (= y x)))
; Reordering the bindings has the same meaning.
(assert (let ((y x) (x 1)) (= y x)))
; q receives the outer p: this asserts outer_p = false.
(assert (let ((p false) (q p)) (= q p)))
; Compound right-hand sides still use the outer x and p.
(assert (let ((x (+ x 1)) (y x) (p (not p)) (q p))
  (and (= x y) (= p q))))
; Local names can change sort: inner x is Bool and inner p is Int.
(assert (let ((x p) (p x)) (= x (> p 0))))
(check-sat)
