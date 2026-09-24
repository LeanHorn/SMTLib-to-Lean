; ----------------------------------------------------------------------------
; flux_bsearch.smt2  --  Flux (CHC for Spacer)
; ----------------------------------------------------------------------------
; Rust     :
;     /// Binary search with an overflow-safe midpoint; overflow checking on.
;     #[opts(check_overflow = "strict")]
;     #[spec(fn(xs: &[i32][@n], k: i32) -> Option<usize{v: v < n}>)]
;     pub fn bsearch(xs: &[i32], k: i32) -> Option<usize> {
;         let mut lo = 0;
;         let mut hi = len(xs);
;         while lo < hi {
;             let mid = lo + (hi - lo) / 2;
;             let x = xs[mid];
;             if x == k {
;                 return Some(mid);
;             }
;             if x < k {
;                 lo = mid + 1;
;             } else {
;                 hi = mid;
;             }
;         }
;         None
;     }
; Input    : Flux constraint for `bsearch` (same function as
;            smt/flux_bsearch_overflow.smt2), before fixpoint solves it.
; Kvars    : k0/k1 = loop invariant over (lo, hi, n, k); k2 = result of the
;            Some(mid) branch. Includes usize/i32 bounds and overflow checks.
; Expected : sat (safe).
; Format   : CHC-COMP style SMT-LIB (set-logic HORN). Translated from the
;            liquid-fixpoint horn format: each kvar $k becomes a predicate,
;            each leaf of the nested forall tree becomes one Horn clause;
;            a concrete head p becomes a query clause (=> (and .. (not p)) false).
;            sat = an inductive invariant exists (program verified),
;            unsat = a counterexample derivation exists.
; ----------------------------------------------------------------------------

(set-logic HORN)
(set-info :status sat)

(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int) (a0 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647)) (k0 0 reftgen$n$0 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647)) (k1 reftgen$n$0 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (not (>= (- a2 a1) 0))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (not (<= (- a2 a1) 18446744073709551615))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (not (>= (+ a1 (div (- a2 a1) 2)) 0))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (not (<= (+ a1 (div (- a2 a1) 2)) 18446744073709551615))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (not (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (not (< a3 a0))) (k0 a1 (+ a1 (div (- a2 a1) 2)) reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (not (< a3 a0))) (k1 (+ a1 (div (- a2 a1) 2)) reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (< a3 a0) (not (>= (+ (+ a1 (div (- a2 a1) 2)) 1) 0))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (< a3 a0) (not (<= (+ (+ a1 (div (- a2 a1) 2)) 1) 18446744073709551615))) false)))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (< a3 a0)) (k0 (+ (+ a1 (div (- a2 a1) 2)) 1) a2 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (distinct a3 a0) (< a3 a0)) (k1 a2 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (not (distinct a3 a0))) (k2 (+ a1 (div (- a2 a1) 2)) reftgen$n$0 a0 a1 a2 a3))))
(assert (forall ((reftgen$n$0 Int) (a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int))
          (=> (and (>= reftgen$n$0 0) (<= reftgen$n$0 18446744073709551615) (>= a0 (- 2147483648)) (<= a0 2147483647) (k0 a1 a2 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (< a1 a2) (< (+ a1 (div (- a2 a1) 2)) reftgen$n$0) (>= a3 (- 2147483648)) (<= a3 2147483647) (not (distinct a3 a0)) (k2 a4 reftgen$n$0 a0 a1 a2 a3) (not (< a4 reftgen$n$0))) false)))

(check-sat)
(exit)
