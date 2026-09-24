; ----------------------------------------------------------------------------
; lh_sets_neg.smt2  --  LiquidHaskell
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/neg/sets01.fq (hand-written LH-style test of
;            the Set theory; one refinement is deliberately wrong)
; Shows    : LH sets as (Array Int Bool) with ((_ map or) ..) for union,
;            extensional set equality. The first check is SAT: that VC is
;            invalid, so fixpoint reports Unsafe.
; Theories : Arrays (z3 map extension) + LIA
; Command  : fixpoint --save sets01.fq
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 5 check-sat: 4 unsat, 1 sat.
;            unsat = the implication (asserted lhs => rhs) is valid.
; ----------------------------------------------------------------------------


(set-option :smt.mbqi false)

(set-option :auto-config false)
(set-option :model true)
(declare-fun set.card ((Array Int Bool)) Int)
(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))
(define-fun SMTLIB_OP_MUL ((x Int) (y Int)) Int (* x y))
(define-fun SMTLIB_OP_DIV ((x Int) (y Int)) Int (div x y))
(define-sort Str () String)
(define-fun strLen ((s Str)) Int (str.len s))
(define-fun subString ((s Str) (i Int) (j Int)) Str (str.substr s i j))
(define-fun concatString ((x Str) (y Str)) Str (str.++ x y))
(declare-fun m2 () (Array Int Bool))
(declare-fun m1 () (Array Int Bool))
(declare-fun cast_as () Int)
(declare-fun m4 () (Array Int Bool))
(declare-fun m3 () (Array Int Bool))
(declare-fun m5 () (Array Int Bool))
(declare-fun VV$35$$35$5 () Int)
(declare-fun VV$35$$35$2 () Int)
(declare-fun VV$35$$35$3 () Int)
(declare-fun VV$35$$35$1 () Int)
(declare-fun VV$35$$35$4 () Int)
(declare-fun cast_as_int () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(define-fun b$36$$35$$35$1 () Bool (= m1 ((as const (Array Int Bool)) false)))
(define-fun b$36$$35$$35$2 () Bool (= m2 ((_ map or) ((_ map or) m1 (store ((as const (Array Int Bool)) false) 10 true)) (store ((as const (Array Int Bool)) false) 20 true))))
(define-fun b$36$$35$$35$3 () Bool (= m3 ((_ map or) ((_ map or) m1 (store ((as const (Array Int Bool)) false) 20 true)) (store ((as const (Array Int Bool)) false) 10 true))))
(define-fun b$36$$35$$35$4 () Bool (= m4 ((_ map or) m1 (store ((as const (Array Int Bool)) false) 10 true))))
(define-fun b$36$$35$$35$5 () Bool (= m5 ((_ map or) m1 (store ((as const (Array Int Bool)) false) 20 true))))
; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$1))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (select m1 100)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$1 b$36$$35$$35$2))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (select m2 100))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$1 b$36$$35$$35$2))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (select m2 10)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$1 b$36$$35$$35$2 b$36$$35$$35$3))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= m2 m3)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$1 b$36$$35$$35$2 b$36$$35$$35$4 b$36$$35$$35$5))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= m2 ((_ map or) m4 m5))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

(pop 1)
; smtBracket - end: sendConcreteBindingsToSMT

(pop 1)
; smtBracket - end: sendConcreteBindingsToSMT

; solve: finished

