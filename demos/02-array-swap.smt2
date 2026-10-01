; Can swapping two different cells twice change memory? Expected: unsat.
; Showcase: symbolic arrays, read/write laws, extensionality, let, and define-fun.
(set-logic ALL)
(define-fun swap ((a (Array Int Int)) (i Int) (j Int)) (Array Int Int)
  (let ((old-i (select a i)) (old-j (select a j)))
    (store (store a i old-j) j old-i)))
(declare-const memory (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (distinct i j))
(assert (distinct (swap (swap memory i j) i j) memory))
(check-sat)
