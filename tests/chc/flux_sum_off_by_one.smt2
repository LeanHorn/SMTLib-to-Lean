; ----------------------------------------------------------------------------
; flux_sum_off_by_one.smt2  --  Flux (CHC for Spacer)
; ----------------------------------------------------------------------------
; Rust     :
;     /// Same loop with an off-by-one bug: `xs[i]` can be out of bounds.
;     #[spec(fn(xs: &[i32][@n]) -> i64)]
;     pub fn sum_buggy(xs: &[i32]) -> i64 {
;         let mut i = 0;
;         let mut acc: i64 = 0;
;         while i <= len(xs) {
;             acc += xs[i] as i64;
;             i += 1;
;         }
;         acc
;     }
; Input    : Flux constraint for `sum_buggy` (loop guard i <= len, then xs[i])
; Kvars    : k0(i, acc, n), k1(acc, n) = loop invariant
; Expected : unsat (unsafe): i = n passes the guard and xs[n] is out of bounds.
; Format   : CHC-COMP style SMT-LIB (set-logic HORN). Translated from the
;            liquid-fixpoint horn format: each kvar $k becomes a predicate,
;            each leaf of the nested forall tree becomes one Horn clause;
;            a concrete head p becomes a query clause (=> (and .. (not p)) false).
;            sat = an inductive invariant exists (program verified),
;            unsat = a counterexample derivation exists.
; ----------------------------------------------------------------------------

(set-logic HORN)
(set-info :status unsat)

(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int))
          (=> (>= reftgen$n$0 0) (k0 0 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int))
          (=> (>= reftgen$n$0 0) (k1 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int))
          (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (<= a0 reftgen$n$0) (not (< a0 reftgen$n$0))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (<= a0 reftgen$n$0) (< a0 reftgen$n$0)) (k0 (+ a0 1) (+ a1 a2) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (<= a0 reftgen$n$0) (< a0 reftgen$n$0)) (k1 (+ a1 a2) reftgen$n$0))))

(check-sat)
(exit)
