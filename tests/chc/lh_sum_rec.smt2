; ----------------------------------------------------------------------------
; lh_sum_rec.smt2  --  LiquidHaskell (CHC for Spacer)
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/horn/pos/sum-rec-ok.smt2 (LH horn constraint)
; Program  : sum n = if n <= 0 then 0 else n + sum (n - 1);  check 0 <= sum y
; Kvars    : k_1(v) = refinement of sum's result (recursive => cyclic clause)
; Expected : sat (safe). Spacer finds k_1(v) := v >= 0.
; Format   : CHC-COMP style SMT-LIB (set-logic HORN). Translated from the
;            liquid-fixpoint horn format: each kvar $k becomes a predicate,
;            each leaf of the nested forall tree becomes one Horn clause;
;            a concrete head p becomes a query clause (=> (and .. (not p)) false).
;            sat = an inductive invariant exists (program verified),
;            unsat = a counterexample derivation exists.
; ----------------------------------------------------------------------------

(set-logic HORN)
(set-info :status sat)

(declare-fun k_1 (Int) Bool)

(assert (forall ((n Int) (cond Bool) (VV Int))
          (=> (and (= cond (<= n 0)) cond (= VV 0)) (k_1 VV))))
(assert (forall ((n Int) (cond Bool) (n1 Int) (t1 Int) (v Int))
          (=> (and (= cond (<= n 0)) (not cond) (= n1 (- n 1)) (k_1 t1) (= v (+ n t1))) (k_1 v))))
(assert (forall ((r Int) (ok1 Bool) (v Bool))
          (=> (and (k_1 r) (= ok1 (<= 0 r)) (= v (<= 0 r)) (= v ok1) (not v)) false)))

(check-sat)
(exit)
