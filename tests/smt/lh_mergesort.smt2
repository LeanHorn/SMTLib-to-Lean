; ----------------------------------------------------------------------------
; lh_mergesort.smt2  --  LiquidHaskell
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/pos/MergeSort.fq (LH output for tests/pos/MergeSort.hs,
;            minimized)
; Shows    : a full program's worth of queries: `len` measure applied through
;            apply##0, kvar solving for split/merge/sort, ~200 check-sats.
; Theories : UF + LIA
; Command  : fixpoint --save MergeSort.fq
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 206 check-sat: 41 unsat, 165 sat.
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
(declare-fun x_Tuple33 () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun GHC.Types.$36$91$36$$36$93$36$$36$35$36$$36$35$36$6m () Int)
(declare-fun lq_karg$36$y$35$$35$ayD$35$$35$k_$35$$35$795 () Int)
(declare-fun x_Tuple55 () Int)
(declare-fun x_Tuple65 () Int)
(declare-fun MergeSort.split$35$$35$rlx () Int)
(declare-fun ds_dMs () Int)
(declare-fun snd () Int)
(declare-fun GHC.Classes.$36$60$36$$36$61$36$$36$35$36$$36$35$36$r4 () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun lq_anf$36$$35$$35$dMW () Int)
(declare-fun lq_karg$36$x$35$$35$ayC$35$$35$k_$35$$35$795 () Int)
(declare-fun len () Int)
(declare-fun ys$35$$35$XAl () Int)
(declare-fun y$35$$35$ayD () Int)
(declare-fun xs$35$$35$aA4 () Int)
(declare-fun lq_karg$36$ds_dMw$35$$35$k_$35$$35$753 () Int)
(declare-fun x_Tuple75 () Int)
(declare-fun fromJust () Int)
(declare-fun x_Tuple73 () Int)
(declare-fun cast_as () Int)
(declare-fun Control.Exception.Base.patError$35$$35$0e () Int)
(declare-fun ds_dMt () Int)
(declare-fun GHC.Types.GT$35$$35$6W () Int)
(declare-fun lq_karg$36$ds_dMt$35$$35$k_$35$$35$795 () Int)
(declare-fun x$35$$35$ayC () Int)
(declare-fun VV$35$$35$50 () Int)
(declare-fun VV$35$$35$30 () Int)
(declare-fun x_Tuple43 () Int)
(declare-fun fst () Int)
(declare-fun lq_karg$36$x$35$$35$ayC$35$$35$k_$35$$35$753 () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun papp2 () Int)
(declare-fun papp7 () Int)
(declare-fun papp1 () Int)
(declare-fun zs$35$$35$ayE () Int)
(declare-fun lq_karg$36$zs$35$$35$ayE$35$$35$k_$35$$35$753 () Int)
(declare-fun lq_karg$36$xs$35$$35$aA4$35$$35$k_$35$$35$795 () Int)
(declare-fun isJust () Int)
(declare-fun papp5 () Int)
(declare-fun MergeSort.merge$35$$35$rly () Int)
(declare-fun null () Int)
(declare-fun lq_karg$36$VV$35$$35$794$35$$35$k_$35$$35$795 () Int)
(declare-fun x_Tuple76 () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Tuple.$36$40$36$$36$44$36$$36$41$36$$36$35$36$$36$35$36$74 () Int)
(declare-fun GHC.Types.False$35$$35$68 () Int)
(declare-fun lq_karg$36$lq_anf$36$$35$$35$dMY$35$$35$k_$35$$35$795 () Int)
(declare-fun GHC.Prim.void$35$$35$$35$0l () Int)
(declare-fun ds_dMw () Int)
(declare-fun runFun () Int)
(declare-fun x_Tuple52 () Int)
(declare-fun GHC.Types.LT$35$$35$6S () Int)
(declare-fun lit$36$36$36$$36$47$36$Users$36$47$36$rjhala$36$47$36$research$36$47$36$stack$36$47$36$liquidhaskell$36$47$36$tests$36$47$36$pos$36$47$36$MergeSort.hs$36$58$36$$36$40$36$48$36$44$36$1$36$41$36$$36$45$36$$36$40$36$52$36$44$36$41$36$41$36$$36$124$36$function$36$32$36$merge () Str)
(declare-fun lq_karg$36$lq_anf$36$$35$$35$dMY$35$$35$k_$35$$35$753 () Int)
(declare-fun lq_karg$36$lq_anf$36$$35$$35$dMW$35$$35$k_$35$$35$753 () Int)
(declare-fun x_Tuple54 () Int)
(declare-fun x_Tuple61 () Int)
(declare-fun x_Tuple71 () Int)
(declare-fun x_Tuple53 () Int)
(declare-fun ys$35$$35$aA5 () Int)
(declare-fun lq_karg$36$zs$35$$35$ayE$35$$35$k_$35$$35$795 () Int)
(declare-fun x_Tuple42 () Int)
(declare-fun Prop () Int)
(declare-fun papp3 () Int)
(declare-fun x_Tuple51 () Int)
(declare-fun lq_karg$36$ds_dMw$35$$35$k_$35$$35$795 () Int)
(declare-fun lq_anf$36$$35$$35$dN0 () Int)
(declare-fun autolen () Int)
(declare-fun x_Tuple62 () Int)
(declare-fun x_Tuple64 () Int)
(declare-fun lq_karg$36$lq_anf$36$$35$$35$dMW$35$$35$k_$35$$35$795 () Int)
(declare-fun x_Tuple66 () Int)
(declare-fun addrLen () Int)
(declare-fun lq_anf$36$$35$$35$dMY () Int)
(declare-fun VV$35$$35$53 () Int)
(declare-fun x_Tuple41 () Int)
(declare-fun x_Tuple72 () Int)
(declare-fun lq_karg$36$ds_dMt$35$$35$k_$35$$35$753 () Int)
(declare-fun MergeSort.sort$35$$35$rjG () Int)
(declare-fun head () Int)
(declare-fun tail () Int)
(declare-fun GHC.Types.EQ$35$$35$6U () Int)
(declare-fun GHC.Types.$36$58$36$$36$35$36$$36$35$36$64 () Int)
(declare-fun x_Tuple74 () Int)
(declare-fun cmp () Int)
(declare-fun lq_karg$36$ds_dMs$35$$35$k_$35$$35$753 () Int)
(declare-fun papp6 () Int)
(declare-fun lq_karg$36$ds_dMs$35$$35$k_$35$$35$795 () Int)
(declare-fun GHC.Types.True$35$$35$6u () Int)
(declare-fun lq_karg$36$VV$35$$35$752$35$$35$k_$35$$35$753 () Int)
(declare-fun cast_as_int () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun x_Tuple63 () Int)
(declare-fun lq_anf$36$$35$$35$dN1 () Int)
(declare-fun lq_karg$36$y$35$$35$ayD$35$$35$k_$35$$35$753 () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(define-fun b$36$$35$$35$64 () Bool (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) 0) (= lq_anf$36$$35$$35$dMW ds_dMs) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (+ 1 (apply$35$$35$0 (as len Int) ds_dMt))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dMW) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dMW) ds_dMt) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dMW) x$35$$35$ayC) (= lq_anf$36$$35$$35$dMW (apply$35$$35$0 (apply$35$$35$0 (as GHC.Types.$36$58$36$$36$35$36$$36$35$36$64 Int) x$35$$35$ayC) ds_dMt)) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (+ 1 (apply$35$$35$0 (as len Int) ds_dMt))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dMW) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dMW) ds_dMt) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dMW) x$35$$35$ayC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) 0)))
(define-fun b$36$$35$$35$4 () Bool (and (= GHC.Types.EQ$35$$35$6U GHC.Types.EQ$35$$35$6U)))
(define-fun b$36$$35$$35$5 () Bool (and (= GHC.Types.LT$35$$35$6S GHC.Types.LT$35$$35$6S)))
(define-fun b$36$$35$$35$6 () Bool (and (= GHC.Types.GT$35$$35$6W GHC.Types.GT$35$$35$6W)))
(define-fun b$36$$35$$35$7 () Bool (and (apply$35$$35$1 Prop GHC.Types.True$35$$35$6u)))
(define-fun b$36$$35$$35$8 () Bool (and (not (apply$35$$35$1 Prop GHC.Types.False$35$$35$68))))
(define-fun b$36$$35$$35$9 () Bool (and (not (apply$35$$35$1 Prop GHC.Types.False$35$$35$68))))
(define-fun b$36$$35$$35$73 () Bool (and (>= (apply$35$$35$0 (as len Int) zs$35$$35$ayE) 0)))
(define-fun b$36$$35$$35$74 () Bool (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) 0) (= lq_anf$36$$35$$35$dMY ds_dMt) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (+ 1 (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dMY) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dMY) zs$35$$35$ayE) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dMY) y$35$$35$ayD) (= lq_anf$36$$35$$35$dMY (apply$35$$35$0 (apply$35$$35$0 (as GHC.Types.$36$58$36$$36$35$36$$36$35$36$64 Int) y$35$$35$ayD) zs$35$$35$ayE)) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (+ 1 (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dMY) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dMY) zs$35$$35$ayE) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dMY) y$35$$35$ayD) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) 0)))
(define-fun b$36$$35$$35$11 () Bool (and (apply$35$$35$1 Prop GHC.Types.True$35$$35$6u)))
(define-fun b$36$$35$$35$75 () Bool (and (= (+ (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as fst Int) ds_dMw)) (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as snd Int) ds_dMw))) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(define-fun b$36$$35$$35$77 () Bool (and (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0)))
(define-fun b$36$$35$$35$78 () Bool (and (>= (apply$35$$35$0 (as len Int) ys$35$$35$XAl) 0)))
(define-fun b$36$$35$$35$79 () Bool (and (= (+ (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as fst Int) ds_dMw)) (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as snd Int) ds_dMw))) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)) (= (apply$35$$35$0 (as snd Int) ds_dMw) ys$35$$35$XAl) (= (apply$35$$35$0 (as fst Int) ds_dMw) xs$35$$35$aA4) (= (apply$35$$35$0 (as x_Tuple22 Int) ds_dMw) ys$35$$35$XAl) (= (apply$35$$35$0 (as x_Tuple21 Int) ds_dMw) xs$35$$35$aA4) (= ds_dMw (apply$35$$35$0 (apply$35$$35$0 (as GHC.Tuple.$36$40$36$$36$44$36$$36$41$36$$36$35$36$$36$35$36$74 Int) xs$35$$35$aA4) ys$35$$35$XAl)) (= (apply$35$$35$0 (as snd Int) ds_dMw) ys$35$$35$XAl) (= (apply$35$$35$0 (as fst Int) ds_dMw) xs$35$$35$aA4) (= (apply$35$$35$0 (as x_Tuple22 Int) ds_dMw) ys$35$$35$XAl) (= (apply$35$$35$0 (as x_Tuple21 Int) ds_dMw) xs$35$$35$aA4)))
(define-fun b$36$$35$$35$82 () Bool (and (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0)))
(define-fun b$36$$35$$35$83 () Bool (and (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (>= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 0)))
(define-fun b$36$$35$$35$84 () Bool (and (= (+ (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as fst Int) ds_dMw)) (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as snd Int) ds_dMw))) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)) (= (apply$35$$35$0 (as snd Int) ds_dMw) ys$35$$35$aA5) (= (apply$35$$35$0 (as fst Int) ds_dMw) xs$35$$35$aA4) (= (apply$35$$35$0 (as x_Tuple22 Int) ds_dMw) ys$35$$35$aA5) (= (apply$35$$35$0 (as x_Tuple21 Int) ds_dMw) xs$35$$35$aA4) (= ds_dMw (apply$35$$35$0 (apply$35$$35$0 (as GHC.Tuple.$36$40$36$$36$44$36$$36$41$36$$36$35$36$$36$35$36$74 Int) xs$35$$35$aA4) ys$35$$35$aA5)) (= (apply$35$$35$0 (as snd Int) ds_dMw) ys$35$$35$aA5) (= (apply$35$$35$0 (as fst Int) ds_dMw) xs$35$$35$aA4) (= (apply$35$$35$0 (as x_Tuple22 Int) ds_dMw) ys$35$$35$aA5) (= (apply$35$$35$0 (as x_Tuple21 Int) ds_dMw) xs$35$$35$aA4)))
(define-fun b$36$$35$$35$54 () Bool (and (>= (apply$35$$35$0 (as len Int) ds_dMs) 0)))
(define-fun b$36$$35$$35$87 () Bool (and (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dN0) (+ 1 (apply$35$$35$0 (as len Int) xs$35$$35$aA4))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dN0) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dN0) xs$35$$35$aA4) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dN0) x$35$$35$ayC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dN0) 0)))
(define-fun b$36$$35$$35$89 () Bool (and (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dN1) (+ 1 (apply$35$$35$0 (as len Int) ys$35$$35$aA5))) (= (apply$35$$35$1 (as null Int) lq_anf$36$$35$$35$dN1) false) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$dN1) ys$35$$35$aA5) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$dN1) y$35$$35$ayD) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dN1) 0)))
(define-fun b$36$$35$$35$316 () Bool (and (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) 0) (= VV$35$$35$50 ys$35$$35$aA5) (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) 0)))
(define-fun b$36$$35$$35$317 () Bool (and (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) 0) (= VV$35$$35$53 xs$35$$35$aA4) (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) 0)))
(define-fun b$36$$35$$35$318 () Bool (and (= (apply$35$$35$0 (as snd Int) VV$35$$35$30) lq_anf$36$$35$$35$dN1) (= (apply$35$$35$0 (as fst Int) VV$35$$35$30) lq_anf$36$$35$$35$dN0) (= (apply$35$$35$0 (as x_Tuple22 Int) VV$35$$35$30) lq_anf$36$$35$$35$dN1) (= (apply$35$$35$0 (as x_Tuple21 Int) VV$35$$35$30) lq_anf$36$$35$$35$dN0)))
(define-fun b$36$$35$$35$63 () Bool (and (>= (apply$35$$35$0 (as len Int) ds_dMt) 0)))
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$64 b$36$$35$$35$4 b$36$$35$$35$5 b$36$$35$$35$6 b$36$$35$$35$7 b$36$$35$$35$8 b$36$$35$$35$9 b$36$$35$$35$73 b$36$$35$$35$74 b$36$$35$$35$11 b$36$$35$$35$77 b$36$$35$$35$78 b$36$$35$$35$79 b$36$$35$$35$54 b$36$$35$$35$317 b$36$$35$$35$63))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$53 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$53 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$53 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$53 lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Unsat
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
(assert (not (>= VV$35$$35$53 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 (apply$35$$35$0 (as fst Int) ds_dMw))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$53 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$53 zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 (apply$35$$35$0 (as snd Int) ds_dMw))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$53 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$53 lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$53 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$53 ds_dMt))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$53 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$53 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$53 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$53 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$53 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$53 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$53 ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$53 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$53 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$53 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$53 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$53 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$53 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$53 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$53) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$53 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$53) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$53) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt))) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))) (not (= xs$35$$35$aA4 lq_anf$36$$35$$35$dMW)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt)) (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (= xs$35$$35$aA4 (apply$35$$35$0 (as fst Int) ds_dMw)) (not (= xs$35$$35$aA4 lq_anf$36$$35$$35$dMY)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (not (= xs$35$$35$aA4 ds_dMt)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))) (not (= xs$35$$35$aA4 ds_dMs)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)))) b$36$$35$$35$64 b$36$$35$$35$4 b$36$$35$$35$5 b$36$$35$$35$6 b$36$$35$$35$7 b$36$$35$$35$8 b$36$$35$$35$9 b$36$$35$$35$73 b$36$$35$$35$74 b$36$$35$$35$11 (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0) b$36$$35$$35$82 b$36$$35$$35$83 b$36$$35$$35$84 b$36$$35$$35$54 b$36$$35$$35$316 b$36$$35$$35$63))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 xs$35$$35$aA4)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4))))
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
(assert (not (= VV$35$$35$50 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 (apply$35$$35$0 (as fst Int) ds_dMw))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 xs$35$$35$aA4))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 xs$35$$35$aA4)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 lq_anf$36$$35$$35$dMY)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 xs$35$$35$aA4)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 ds_dMs))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 ds_dMs)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 (apply$35$$35$0 (as snd Int) ds_dMw))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 xs$35$$35$aA4)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) zs$35$$35$ayE) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= VV$35$$35$50 zs$35$$35$ayE)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMs) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> VV$35$$35$50 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= VV$35$$35$50 ds_dMt)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 ds_dMt))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= VV$35$$35$50 xs$35$$35$aA4)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) ds_dMt))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) ds_dMt) (apply$35$$35$0 (as len Int) ds_dMs)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY) (apply$35$$35$0 (as len Int) ds_dMt)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (not (= VV$35$$35$50 zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (=> (> (apply$35$$35$0 (as len Int) VV$35$$35$50) 1) (< (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< VV$35$$35$50 lq_anf$36$$35$$35$dMW)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$50) (+ (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$50) (apply$35$$35$0 (as len Int) xs$35$$35$aA4))))
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
(assert (and (and (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt))) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))) (not (= xs$35$$35$aA4 lq_anf$36$$35$$35$dMW)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt)) (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (= xs$35$$35$aA4 (apply$35$$35$0 (as fst Int) ds_dMw)) (not (= xs$35$$35$aA4 lq_anf$36$$35$$35$dMY)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (not (= xs$35$$35$aA4 ds_dMt)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMt)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))) (not (= xs$35$$35$aA4 ds_dMs)) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs)) (<= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)) (=> (> (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 1) (< (apply$35$$35$0 (as len Int) xs$35$$35$aA4) (apply$35$$35$0 (as len Int) ds_dMs))) (not (= ys$35$$35$aA5 lq_anf$36$$35$$35$dMW)) (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMs))) (not (= ys$35$$35$aA5 lq_anf$36$$35$$35$dMY)) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (<= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY)) (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW))) (<= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMs)) (>= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 0) (<= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (<= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMt)) (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) zs$35$$35$ayE))) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMs)) (<= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) zs$35$$35$ayE)) (not (= ys$35$$35$aA5 ds_dMs)) (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMY))) (=> (> (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 1) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMt))) (= ys$35$$35$aA5 (apply$35$$35$0 (as snd Int) ds_dMw)) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$dMW)) (not (= ys$35$$35$aA5 ds_dMt)) (< (apply$35$$35$0 (as len Int) ys$35$$35$aA5) (apply$35$$35$0 (as len Int) ds_dMt))) b$36$$35$$35$64 b$36$$35$$35$4 b$36$$35$$35$5 b$36$$35$$35$6 b$36$$35$$35$7 b$36$$35$$35$8 b$36$$35$$35$9 b$36$$35$$35$73 b$36$$35$$35$74 b$36$$35$$35$11 b$36$$35$$35$75 (>= (apply$35$$35$0 (as len Int) xs$35$$35$aA4) 0) (>= (apply$35$$35$0 (as len Int) ys$35$$35$aA5) 0) b$36$$35$$35$54 b$36$$35$$35$87 b$36$$35$$35$89 b$36$$35$$35$318 b$36$$35$$35$63))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (+ (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as fst Int) VV$35$$35$30)) (apply$35$$35$0 (as len Int) (apply$35$$35$0 (as snd Int) VV$35$$35$30))) (apply$35$$35$0 (as len Int) ds_dMs))))
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

