; ----------------------------------------------------------------------------
; lh_polyset_adt_sets.smt2  --  LiquidHaskell
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/pos/polyset.fq (LH output for a PolySet module)
; Shows    : parametric datatype nested in itself, Set-valued measure lstHd
;            encoded as (Array (PolySet.Lst Int) Bool), const-array + store.
; Theories : DT + Arrays + UF
; Command  : fixpoint --save polyset.fq
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 1 check-sat: 1 unsat, 0 sat.
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
(declare-datatypes ((PolySet.Lst 1)) ((par (T0) ((PolySet.Cons (PolySet.hd T0) (PolySet.tl (PolySet.Lst T0))) (PolySet.Emp)))))
(declare-fun p () (PolySet.Lst Int))
(declare-fun cast_as () Int)
(declare-fun PolySet.lstHd () Int)
(declare-fun VV$35$$35$4 () (PolySet.Lst (PolySet.Lst Int)))
(declare-fun cast_as_int () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(declare-fun apply$35$$35$0 (Int (PolySet.Lst (PolySet.Lst Int))) (Array (PolySet.Lst Int) Bool))
(declare-fun coerce$35$$35$0 ((PolySet.Lst (PolySet.Lst Int))) (Array (PolySet.Lst Int) Bool))
(declare-fun smt_lambda$35$$35$0 ((PolySet.Lst (PolySet.Lst Int)) (Array (PolySet.Lst Int) Bool)) Int)
(define-fun b$36$$35$$35$4 () Bool (and (is-PolySet.Cons VV$35$$35$4) (not (is-PolySet.Emp VV$35$$35$4)) (= VV$35$$35$4 ((as PolySet.Cons (PolySet.Lst (PolySet.Lst Int))) p (as PolySet.Emp (PolySet.Lst (PolySet.Lst Int))))) (= (PolySet.hd VV$35$$35$4) p) (= (PolySet.tl VV$35$$35$4) (as PolySet.Emp (PolySet.Lst (PolySet.Lst Int)))) (= (apply$35$$35$0 (as PolySet.lstHd Int) VV$35$$35$4) (store ((as const (Array (PolySet.Lst Int) Bool)) false) p true))))
; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$4))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$4 ((as PolySet.Cons (PolySet.Lst (PolySet.Lst Int))) p (as PolySet.Emp (PolySet.Lst (PolySet.Lst Int)))))))
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

