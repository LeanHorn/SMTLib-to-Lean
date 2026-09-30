; Feature tour: five queries, one generated Lean file.
; Run: lake exe smt2lean demo.smt2 --out demo-output
; Then: lake env lean demo-output/Query.lean
; Statements come first; replace sorry in the proofs below them.
; The separate demo-chc.smt2 exercises HORN's satisfying-relations target.

; Metadata and solver controls are recorded, never used to prove a query.
(set-info :smt-lib-version 2.6)
(set-info :source "SMTLib-to-Lean feature tour")
(set-info :category "crafted")
(set-info :license "MIT")
(set-info :notes "Bool, Int, bindings, quantifiers, and incremental scopes")
(set-info :status unknown)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-option :print-success true)
(set-option :random-seed 42)
(set-logic ALL)

; Query 1: equal inputs cannot give different outputs of the same function.
; An approachable first Lean proof: intro f x y h; exact h.2 (congrArg f h.1)
(push 1)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (! (= x y) :named |equal inputs|))
(assert (not (= (f x) (f y))))
(check-sat)
(pop 1)

; Query 2: Boolean connectives, equality, distinct, functions, and nested ite.
; xor requires p and q to differ; the final equality requires them to agree.
(push 1)
(declare-const p Bool)
(declare-fun q () Bool)
(declare-const |fallback flag| Bool)
(declare-fun flip (Bool) Bool)
(assert (! (xor p q) :named exclusive))
(assert (and (or p q false) (=> p (not q) true)))
(assert (= (xor p q false) exclusive))
(assert (distinct p false))
(assert (not (distinct p q |fallback flag|)))
(assert (= (ite p (flip q) |fallback flag|)
           (ite (ite p true false) (flip q) |fallback flag|)))
(assert (= p q |fallback flag|))
(check-sat)
(pop 1)

; Queries 3-4: aliases, definitions, exact arithmetic, and scoped assertions.
; push/pop accept multiple levels; zero leaves the current scope unchanged.
(push 2)
(push 0)
(pop 0)
(define-sort Score () Int)
(define-sort Id (T) T)
(declare-const x (Id Score))
(declare-const y Score)
(declare-const z Score)
(declare-const enabled Bool)
(declare-fun score (Bool Int) Int)
(declare-fun accepts (Int Bool) Bool)
(define-fun one () Score 1)
(define-fun inc ((n Score)) Score (+ n one))
(define-fun positive-value ((n Score)) Bool (> n 0))
(define-fun next () Score (inc x))
(define-fun choose ((b Bool) (n Score) (m Score)) Score (ite b (inc n) (- m)))
(assert (! (positive-value x) :named positive))
(assert (and (< 0 x y z) (<= x y z) (> z y x 0) (>= z y x)))
(assert (distinct x y z))
(assert (= (- (+ x y z) y z) x))
(assert (= (* x y z) (* z y x)))
(assert (= (abs (- x)) (abs x)))
(assert (= (- 340282366920938463463374607431768211457)
           (- 0 340282366920938463463374607431768211457)))
; A named Int subterm can be reused, just like a named Boolean assertion.
(assert (= (! next :named |next value|) (+ x one)))
(assert (= (score (xor enabled false) (inc (inc x))) |next value|))
(assert (accepts (choose enabled x y) (ite enabled positive (not positive))))
; let bindings are simultaneous: old refers to the outer x, not the new x.
; The definition next also keeps its original global x beneath this shadowing.
(assert (let ((x (inc x)) (old x))
          (let ((twice (+ x x)))
            (and (= x (+ old one)) (= next x) (= twice (* 2 (inc old)))))))
; Query 3 is contradictory: x is positive and not positive.
(push 1)
(assert (not positive))
(check-sat)
; Query 4 restores the consistent state: its refutation cannot be proved.
(pop 1)
(set-option :print-success false)
(set-info :status unknown)
(check-sat)
(pop 2)

; Query 5: quantifiers, hints, shadowing, and names reused after pop.
; Score, x, and inc now have Boolean types; their earlier meanings are gone.
(push 1)
(define-sort Score () Bool)
(declare-const x Score)
(declare-fun unused (Int Bool) Bool)
(declare-fun P (Int) Bool)
(declare-fun R (Int Bool) Bool)
(define-fun inc ((b Score)) Score (not b))
(assert (forall ((n Int))
          (! (P n) :pattern ((P n)) :no-pattern (P (+ n 1)) :qid all-integers)))
(assert (forall ((n Int) (b Bool))
          (! (R n b) :pattern ((R n b)) :qid all-pairs)))
; Save the global Boolean x, then shadow x twice with integer binders.
(assert (let ((saved x))
          (forall ((x Int))
            (let ((outer x))
              (exists ((x Int) (b Bool))
                (and (= x (+ outer 1)) (= b saved) (R x (inc b))))))))
; Unused binders and a Boolean definition used inside a quantifier.
(assert (forall ((unused Int) (x Bool)) (= (inc x) (not x))))
(assert (exists ((n Int)) (not (P n))))
(check-sat)
(pop 1)
(exit)
