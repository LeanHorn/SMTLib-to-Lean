; Self recursion, simultaneous mutual recursion, ordinary definitions, and lets.
(set-logic ALL)
(define-fun inc ((n Int)) Int (+ n 1))
(define-fun-rec fib ((n Int)) Int
  (ite (<= n 0) 0 (ite (= n 1) 1
    (let ((a (fib (- n 1))) (b (fib (- n 2)))) (+ a b)))))
(define-funs-rec
  ((left ((n Int)) Int) (right ((n Int)) Int))
  ((ite (<= n 0) n (inc (right (- n 1))))
   (ite (<= n 0) n (inc (left (- n 1))))))
(assert (not (= (fib 4) 3)))
(check-sat)
