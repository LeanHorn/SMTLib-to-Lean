; ----------------------------------------------------------------------------
; lh_ple_list_len_adt.smt2  --  LiquidHaskell
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/proof/list01_adt.fq (hand-written in LH's
;            reflection style: reflected `len` over a `Vec` datatype)
; Shows    : Proof by Logical Evaluation (PLE): fixpoint unfolds `len` step by
;            step, asking z3 which constructor guard holds, then checks
;            len [1,2,3] = 3 with the unfolded equations.
; Theories : DT (declare-datatypes, is-/selectors, `as` casts) + UF + LIA
; Command  : fixpoint --save list01_adt.fq   (file sets --rewrite)
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 14 check-sat: 5 unsat, 9 sat.
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
(declare-datatypes ((Vec 1)) ((par (T0) ((VNil) (VCons (head T0) (tail (Vec T0)))))))
(declare-fun len () Int)
(declare-fun cast_as () Int)
(declare-fun VV$35$$35$1 () Int)
(declare-fun cast_as_int () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert true)
; smtBracket - start: filterValidRHS

(push 1)
(declare-fun apply$35$$35$0 (Int (Vec Int)) Int)
(declare-fun coerce$35$$35$0 ((Vec Int)) Int)
(declare-fun smt_lambda$35$$35$0 ((Vec Int) Int) Int)
(assert (not (= (apply$35$$35$0 (as len Int) ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))) 3)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

(pop 1)
; smtBracket - end: sendConcreteBindingsToSMT

(pop 1)
; smtBracket - end: sendConcreteBindingsToSMT

; solve: ple

; smtBracket - start: PLE.withAssms

(push 1)
; smtBracket - start: checkValidWithContext

(push 1)
(assert (not false))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

(assert true)
; smtBracket - start: checkValidWithContext

(push 1)
(assert (not (is-VNil ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (is-VNil ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (not false))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

(declare-fun apply$35$$35$0 (Int (Vec Int)) Int)
(declare-fun coerce$35$$35$0 ((Vec Int)) Int)
(declare-fun smt_lambda$35$$35$0 ((Vec Int) Int) Int)
(assert (= (apply$35$$35$0 (as len Int) ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))) (+ 1 (apply$35$$35$0 (as len Int) (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))))
; smtBracket - start: checkValidWithContext

(push 1)
(assert (not (is-VNil (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (is-VNil (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (not false))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

(assert (= (apply$35$$35$0 (as len Int) (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))) (+ 1 (apply$35$$35$0 (as len Int) (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))))))
; smtBracket - start: checkValidWithContext

(push 1)
(assert (not (is-VNil (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (is-VNil (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (not false))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

(assert (= (apply$35$$35$0 (as len Int) (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))) (+ 1 (apply$35$$35$0 (as len Int) (tail (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))))))
; smtBracket - start: checkValidWithContext

(push 1)
(assert (not (is-VNil (tail (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: checkValidWithContext

; smtBracket - start: checkValidWithContext

(push 1)
(assert (not false))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: checkValidWithContext

(assert (= (apply$35$$35$0 (as len Int) (tail (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))) 0))
(pop 1)
; smtBracket - end: PLE.withAssms

; solve: pos-ple check

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(declare-fun apply$35$$35$0 (Int (Vec Int)) Int)
(declare-fun coerce$35$$35$0 ((Vec Int)) Int)
(declare-fun smt_lambda$35$$35$0 ((Vec Int) Int) Int)
(define-fun b$36$$35$$35$0 () Bool (and (= (apply$35$$35$0 (as len Int) ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))) (+ 1 (apply$35$$35$0 (as len Int) (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))) (= (apply$35$$35$0 (as len Int) (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))) (+ 1 (apply$35$$35$0 (as len Int) (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))))) (= (apply$35$$35$0 (as len Int) (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))))) (+ 1 (apply$35$$35$0 (as len Int) (tail (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))))) (= (apply$35$$35$0 (as len Int) (tail (tail (tail ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int))))))))) 0)))
; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$0))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) ((as VCons (Vec Int)) 1 ((as VCons (Vec Int)) 2 ((as VCons (Vec Int)) 3 (as VNil (Vec Int)))))) 3)))
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

