; CHC tour: a bounded counter, an impossible safety condition, then restoration.
; Run: lake exe smt2lean demo-chc.smt2 --out demo-chc-output
; Then: lake env lean demo-chc-output/Query.lean
; HORN generates Problem_N: there exist relations satisfying every clause.
; The translator constructs these goals; it does not solve them or run Flex.
(set-logic HORN)
(set-info :status unknown)
(define-sort Counter () Int)
(declare-fun Reach (Counter) Bool)
(declare-fun Marked (Counter Bool) Bool)
(declare-fun ready () Bool)
(define-fun zero () Counter 0)
(define-fun inc ((n Counter)) Counter (+ n 1))
(define-fun can-step ((n Counter)) Bool (and (Reach n) (< n 10)))

; Facts, including a named fact reusable as a relation premise.
(assert (! (Reach zero) :named entry))
(assert ready)
; A recursive rule; definitions and hints work inside CHCs too.
(assert (! (forall ((n Counter))
             (! (=> (can-step n) (Reach (inc n)))
                :pattern ((Reach n)) :qid counter-step)) :named step))
; Two relation premises: a nonlinear Horn clause, with an integer guard.
(assert (forall ((x Counter) (y Counter))
          (=> (and (Reach x) (Reach y) (<= (+ x y) 10)) (Reach (+ x y)))))
; Mixed Bool/Int arguments, let, ite, xor/distinct, and nested implications.
(assert (forall ((n Counter) (b Bool))
          (let ((next (ite b (inc n) n)) (flag (xor b false)))
            (=> entry (=> (and ready (Reach n) (< n 10) (distinct n 10))
                          (Marked next flag))))))
; False heads express safety: a reachable or marked counter cannot be negative.
(assert (! (forall ((n Counter)) (=> (and (Reach n) (< n 0)) false)) :named safety))
(assert (forall ((n Counter) (b Bool))
          (=> (and (Marked n b) (or (< n 0) (> n 10))) false)))
; Query 1 has a model: Reach(n) = 0 <= n <= 10,
; Marked(n,b) = 0 <= n <= 10, and ready = true.
(check-sat)

; Query 2 has no model: the counter reaches 5, but this clause forbids it.
(push 1)
(assert (! (=> (Reach 5) false) :named |impossible safety|))
(check-sat)
; Query 3 restores the original, satisfiable CHC problem.
(pop 1)
(check-sat)
(exit)
