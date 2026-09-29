; All right-hand sides use the outer scope, before any new binding is visible.
(set-logic LIA)
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
; Nested bindings see the enclosing let; repeated uses retain the same expression.
(assert (let ((next (+ x 1)) (saved p))
  (let ((x next) (p (not saved)) (old x))
    (and (= (+ x x) (+ old 2)) (= p saved)))))
; Aliases of global names survive shadowing by quantifiers and another let.
(assert (let ((savedX x) (savedP p))
  (forall ((x Int) (p Bool))
    (let ((x (+ x 1)) (p (not p)))
      (and (= x savedX) (= p savedP))))))
; Aliases of bound variables survive inner binders, then the outer scope resumes.
(assert (forall ((x Int) (p Bool))
  (let ((savedX x) (savedP p))
    (and (exists ((x Int) (p Bool)) (and (= x savedX) (= p savedP)))
         (= x savedX) (= p savedP)))))
; The same syntax in sibling scopes must expand with each scope's own bindings.
(assert (and (let ((x 1) (p true)) (= p (> x 0)))
             (let ((x 2) (p false)) (= p (> x 0)))
             (= p (> x 0))))
(check-sat)
