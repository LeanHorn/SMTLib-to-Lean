; ----------------------------------------------------------------------------
; lh_abs_neg.smt2  --  LiquidHaskell (CHC for Spacer)
; ----------------------------------------------------------------------------
; Input    : liquid-fixpoint tests/horn/neg/abs02-re.smt2 (LH horn constraint)
; Program  : abs x = if x >= 0 then x else 0 - x; incr r = r + 1 with r >= 0;
;            asserts 6660 <= incr .. which does not hold.
; Kvars    : k_1(v, x) for abs's result, k_3(v, z) for the incremented value
; Expected : unsat (unsafe): res = 1 reaches the failing assertion.
; Format   : CHC-COMP style SMT-LIB (set-logic HORN). Translated from the
;            liquid-fixpoint horn format: each kvar $k becomes a predicate,
;            each leaf of the nested forall tree becomes one Horn clause;
;            a concrete head p becomes a query clause (=> (and .. (not p)) false).
;            sat = an inductive invariant exists (program verified),
;            unsat = a counterexample derivation exists.
; ----------------------------------------------------------------------------

(set-logic HORN)
(set-info :status unsat)

(declare-fun k_1 (Int Int) Bool)
(declare-fun k_3 (Int Int) Bool)

(assert (forall ((x Int) (pos Bool) (VV Int))
          (=> (and (= pos (>= x 0)) pos (= VV x)) (k_1 VV x))))
(assert (forall ((x Int) (pos Bool) (v Int))
          (=> (and (= pos (>= x 0)) (not pos) (= v (- 0 x))) (k_1 v x))))
(assert (forall ((z Int) (r Int) (v Int))
          (=> (and (>= r 0) (= v (+ r 1))) (k_3 v z))))
(assert (forall ((_t1 Int) (VV_0 Int))
          (=> (and (>= _t1 0) (k_1 VV_0 _t1) (not (>= VV_0 0))) false)))
(assert (forall ((z Int) (res Int) (ok Bool) (v Bool))
          (=> (and (k_3 res z) (= ok (<= 6660 res)) (= v (<= 6660 res)) (= v ok) (not v)) false)))

(check-sat)
(exit)
