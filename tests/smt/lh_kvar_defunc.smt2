; ----------------------------------------------------------------------------
; lh_kvar_defunc.smt2  --  LiquidHaskell
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/pos/test00.hs.fq (emitted by LH for Test0.hs)
; Shows    : kvar inference by qualifier filtering (many push/assert/check-sat
;            rounds), GHC-mangled names, Bool-as-Int via `Prop`, higher-order
;            values defunctionalized to apply##N / coerce##N / smt_lambda##N.
; Theories : UF + LIA (+ String preamble)
; Command  : fixpoint --save test00.hs.fq
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 16 check-sat: 4 unsat, 12 sat.
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
(declare-fun x_Tuple77 () Int)
(declare-fun x_Tuple44 () Int)
(declare-fun lq_karg$36$VV$35$234$35$$35$k_235 () Int)
(declare-fun lq_karg$36$GHC.Types.GT$35$6W$35$$35$k_273 () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun lq_karg$36$fix$35$GHC.Classes.$35$36$35$fOrdInt$35$35$35$rhx$35$$35$k_273 () Int)
(declare-fun lq_anf__d16B () Int)
(declare-fun x_Tuple55 () Int)
(declare-fun x_Tuple65 () Int)
(declare-fun VV$35$$35$8 () Int)
(declare-fun fix$35$GHC.Classes.$35$36$35$fOrdInt$35$35$35$rhx () Int)
(declare-fun snd () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun lq_anf__d16y () Int)
(declare-fun len () Int)
(declare-fun fix$35$$35$36$35$dOrd_a165 () Int)
(declare-fun x_Tuple75 () Int)
(declare-fun fromJust () Int)
(declare-fun x_Tuple73 () Int)
(declare-fun cast_as () Int)
(declare-fun lq_anf__d16A () Int)
(declare-fun GHC.Types.GT$35$6W () Int)
(declare-fun lq_anf__d16C () Int)
(declare-fun x_Tuple43 () Int)
(declare-fun fst () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun papp2 () Int)
(declare-fun lq_karg$36$fix$35$$35$36$35$dNum_a166$35$$35$k_235 () Int)
(declare-fun papp1 () Int)
(declare-fun VV$35$$35$6 () Int)
(declare-fun xsListSelector () Int)
(declare-fun isJust () Int)
(declare-fun null () Int)
(declare-fun x_Tuple76 () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.True$35$6u () Int)
(declare-fun lq_karg$36$fix$35$GHC.Classes.$35$36$35$fOrdInt$35$35$35$rhx$35$$35$k_235 () Int)
(declare-fun VV$35$346 () Int)
(declare-fun lq_karg$36$GHC.Types.EQ$35$6U$35$$35$k_273 () Int)
(declare-fun fix$35$$35$36$35$dNum_a166 () Int)
(declare-fun GHC.Types.LT$35$6S () Int)
(declare-fun a_a164 () Int)
(declare-fun gooberding$35$a15N () Int)
(declare-fun lq_karg$36$fix$35$$35$36$35$dOrd_a165$35$$35$k_235 () Int)
(declare-fun x_Tuple52 () Int)
(declare-fun lq_karg$36$GHC.Types.LT$35$6S$35$$35$k_235 () Int)
(declare-fun lq_anf__d16x () Int)
(declare-fun x_Tuple54 () Int)
(declare-fun x_Tuple61 () Int)
(declare-fun x_Tuple71 () Int)
(declare-fun x_Tuple53 () Int)
(declare-fun lq_karg$36$VV$35$272$35$$35$k_273 () Int)
(declare-fun VV$35$$35$2 () Int)
(declare-fun xListSelector () Int)
(declare-fun x_Tuple42 () Int)
(declare-fun lq_karg$36$GHC.Types.LT$35$6S$35$$35$k_273 () Int)
(declare-fun Prop () Int)
(declare-fun fix$35$GHC.Num.$35$36$35$fNumInt$35$35$35$rhy () Int)
(declare-fun papp3 () Int)
(declare-fun x_Tuple51 () Int)
(declare-fun lq_karg$36$fix$35$GHC.Num.$35$36$35$fNumInt$35$35$35$rhy$35$$35$k_235 () Int)
(declare-fun lq_karg$36$GHC.Types.GT$35$6W$35$$35$k_235 () Int)
(declare-fun x_Tuple62 () Int)
(declare-fun x_Tuple64 () Int)
(declare-fun x_Tuple66 () Int)
(declare-fun addrLen () Int)
(declare-fun x_Tuple41 () Int)
(declare-fun x_Tuple72 () Int)
(declare-fun GHC.Types.EQ$35$6U () Int)
(declare-fun Test0.x$35$r12i () Int)
(declare-fun lq_anf__d16w () Int)
(declare-fun x_Tuple74 () Int)
(declare-fun lq_karg$36$GHC.Types.EQ$35$6U$35$$35$k_235 () Int)
(declare-fun cmp () Int)
(declare-fun lq_karg$36$fix$35$GHC.Num.$35$36$35$fNumInt$35$35$35$rhy$35$$35$k_273 () Int)
(declare-fun lq_anf__d16z () Int)
(declare-fun VV$35$373 () Int)
(declare-fun cast_as_int () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun x_Tuple63 () Int)
(declare-fun GHC.Types.False$35$68 () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(define-fun b$36$$35$$35$33 () Bool (and (= (apply$35$$35$0 cmp GHC.Types.EQ$35$6U) GHC.Types.EQ$35$6U)))
(define-fun b$36$$35$$35$34 () Bool (and (= (apply$35$$35$0 cmp GHC.Types.LT$35$6S) GHC.Types.LT$35$6S)))
(define-fun b$36$$35$$35$35 () Bool (and (= (apply$35$$35$0 cmp GHC.Types.GT$35$6W) GHC.Types.GT$35$6W)))
(define-fun b$36$$35$$35$40 () Bool (and (= lq_anf__d16w 0)))
(define-fun b$36$$35$$35$41 () Bool (and (= lq_anf__d16x lq_anf__d16w)))
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(define-fun b$36$$35$$35$73 () Bool (and (= (apply$35$$35$1 Prop VV$35$373) (>= gooberding$35$a15N lq_anf__d16x)) (= VV$35$373 lq_anf__d16y)))
(define-fun b$36$$35$$35$10 () Bool (and (apply$35$$35$1 Prop GHC.Types.True$35$6u)))
(define-fun b$36$$35$$35$42 () Bool (and (= (apply$35$$35$1 Prop lq_anf__d16y) (>= gooberding$35$a15N lq_anf__d16x))))
(define-fun b$36$$35$$35$11 () Bool (and (not (apply$35$$35$1 Prop GHC.Types.False$35$68))))
(define-fun b$36$$35$$35$43 () Bool (and (= lq_anf__d16z 0)))
(define-fun b$36$$35$$35$45 () Bool (and (= lq_anf__d16A 0)))
(define-fun b$36$$35$$35$46 () Bool (and (= (apply$35$$35$1 Prop lq_anf__d16B) (> Test0.x$35$r12i lq_anf__d16A))))
(define-fun b$36$$35$$35$47 () Bool (and (= (apply$35$$35$1 Prop lq_anf__d16C) (> Test0.x$35$r12i lq_anf__d16A)) (= lq_anf__d16C lq_anf__d16B)))
(define-fun b$36$$35$$35$50 () Bool (and (= (apply$35$$35$1 Prop lq_anf__d16C) (> Test0.x$35$r12i lq_anf__d16A)) (= lq_anf__d16C lq_anf__d16B)))
(define-fun b$36$$35$$35$51 () Bool (and (= (apply$35$$35$1 Prop lq_anf__d16C) (> Test0.x$35$r12i lq_anf__d16A)) (= lq_anf__d16C lq_anf__d16B) (apply$35$$35$1 Prop lq_anf__d16C) (apply$35$$35$1 Prop lq_anf__d16C)))
(define-fun b$36$$35$$35$85 () Bool (and (= (apply$35$$35$1 Prop VV$35$$35$8) (>= gooberding$35$a15N lq_anf__d16x)) (= VV$35$$35$8 lq_anf__d16y)))
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$33 b$36$$35$$35$34 b$36$$35$$35$35 b$36$$35$$35$10 b$36$$35$$35$11 b$36$$35$$35$43))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$6 0))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$6 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$33 b$36$$35$$35$34 b$36$$35$$35$35 b$36$$35$$35$10 b$36$$35$$35$11 b$36$$35$$35$45 b$36$$35$$35$46 b$36$$35$$35$47 b$36$$35$$35$50 b$36$$35$$35$51 (= VV$35$$35$2 Test0.x$35$r12i) (= VV$35$346 Test0.x$35$r12i)))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$2 0))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$2 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$2 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$2 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$2 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$2 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (not (= gooberding$35$a15N 0)) (>= gooberding$35$a15N 0) (> gooberding$35$a15N 0)) b$36$$35$$35$33 b$36$$35$$35$34 b$36$$35$$35$35 b$36$$35$$35$40 b$36$$35$$35$41 b$36$$35$$35$73 b$36$$35$$35$10 b$36$$35$$35$42 b$36$$35$$35$11 b$36$$35$$35$85))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (apply$35$$35$1 Prop VV$35$$35$8)))
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

