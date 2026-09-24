; ----------------------------------------------------------------------------
; flux_bsearch_overflow.smt2  --  Flux
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
; Shows    : loop-invariant (kvar) inference by qualifier filtering, usize/i32
;            range facts, overflow checks (check_overflow = strict), integer
;            division in the midpoint lo + (hi - lo) / 2.
; Theories : UF + LIA (div by constant)
; Produced : cargo flux (dump_constraint = true) -> log/fluxq.bsearch.smt2 (fixpoint
;            horn), then fixpoint --save --allowho --allowhoqs --solver=z3
;            (the flags Flux itself passes to fixpoint).
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 72 check-sat: 37 unsat, 35 sat.
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
(declare-fun le () Int)
(declare-fun nnf_arg$36$$35$$35$k2$35$$35$5 () Int)
(declare-fun reftgen$36$n$36$0 () Int)
(declare-fun a3 () Int)
(declare-fun fix$36$_$36$$35$6 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$0$35$$35$k2 () Int)
(declare-fun a0 () Int)
(declare-fun ge () Int)
(declare-fun fix$36$_$36$$35$8$35$$35$5 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$1$35$$35$k2 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$3$35$$35$k2 () Int)
(declare-fun nnf_arg$36$$35$$35$k0$35$$35$1 () Int)
(declare-fun cast_as () Int)
(declare-fun gt () Int)
(declare-fun nnf_arg$36$$35$$35$k1$35$$35$2 () Int)
(declare-fun fix$36$_$36$$35$1 () Int)
(declare-fun fix$36$_$36$$35$14$35$$35$12 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$2$35$$35$k2 () Int)
(declare-fun nnf_arg$36$$35$$35$k2$35$$35$1 () Int)
(declare-fun nnf_arg$36$$35$$35$k1$35$$35$1 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k1$35$$35$2$35$$35$k1 () Int)
(declare-fun fix$36$_$36$$35$15 () Int)
(declare-fun fix$36$_$36$$35$13$35$$35$8 () Int)
(declare-fun fix$36$_$36$$35$13 () Int)
(declare-fun fix$36$_$36$$35$14$35$$35$13 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k0$35$$35$2$35$$35$k0 () Int)
(declare-fun fix$36$_$36$$35$14$35$$35$10 () Int)
(declare-fun a1 () Int)
(declare-fun fix$36$_$36$$35$2 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$4$35$$35$k2 () Int)
(declare-fun fix$36$_$36$$35$15$35$$35$14 () Int)
(declare-fun fix$36$_$36$$35$16$35$$35$15 () Int)
(declare-fun fix$36$_$36$$35$7$35$$35$4 () Int)
(declare-fun a2 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k1$35$$35$0$35$$35$k1 () Int)
(declare-fun fix$36$_$36$$35$11 () Int)
(declare-fun fix$36$_$36$$35$9 () Int)
(declare-fun fix$36$_$36$$35$16 () Int)
(declare-fun lt () Int)
(declare-fun fix$36$_$36$$35$5$35$$35$1 () Int)
(declare-fun nnf_arg$36$$35$$35$k2$35$$35$2 () Int)
(declare-fun nnf_arg$36$$35$$35$k2$35$$35$4 () Int)
(declare-fun fix$36$_$36$$35$13$35$$35$9 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k0$35$$35$0$35$$35$k0 () Int)
(declare-fun fix$36$_$36$$35$7$35$$35$3 () Int)
(declare-fun nnf_arg$36$$35$$35$k0$35$$35$2 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k0$35$$35$1$35$$35$k0 () Int)
(declare-fun fix$36$_$36$$35$10 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k1$35$$35$1$35$$35$k1 () Int)
(declare-fun fix$36$_$36$$35$5$35$$35$2 () Int)
(declare-fun fix$36$_$36$$35$8$35$$35$7 () Int)
(declare-fun a4 () Int)
(declare-fun fix$36$_$36$$35$14$35$$35$11 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k0$35$$35$3$35$$35$k0 () Int)
(declare-fun fix$36$_$36$$35$7 () Int)
(declare-fun nnf_arg$36$$35$$35$k0$35$$35$3 () Int)
(declare-fun nnf_arg$36$$35$$35$k2$35$$35$3 () Int)
(declare-fun lq_karg$36$nnf_arg$36$$35$$35$k2$35$$35$5$35$$35$k2 () Int)
(declare-fun fix$36$_$36$$35$14 () Int)
(declare-fun fix$36$_$36$$35$8$35$$35$6 () Int)
(declare-fun fix$36$_$36$ () Int)
(declare-fun fix$36$_$36$$35$3 () Int)
(declare-fun cast_as_int () Int)
(declare-fun fix$36$_$36$$35$12 () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(define-fun b$36$$35$$35$35 () Bool (< a1 a2))
(define-fun b$36$$35$$35$36 () Bool (< a1 a2))
(define-fun b$36$$35$$35$40 () Bool (not (< a3 a0)))
(define-fun b$36$$35$$35$41 () Bool (not (< a3 a0)))
(define-fun b$36$$35$$35$42 () Bool (< a3 a0))
(define-fun b$36$$35$$35$43 () Bool (< a3 a0))
(define-fun b$36$$35$$35$12 () Bool (>= reftgen$36$n$36$0 0))
(define-fun b$36$$35$$35$44 () Bool (< a3 a0))
(define-fun b$36$$35$$35$13 () Bool (<= reftgen$36$n$36$0 18446744073709551615))
(define-fun b$36$$35$$35$45 () Bool (< a3 a0))
(define-fun b$36$$35$$35$14 () Bool (>= a0 (- 2147483648)))
(define-fun b$36$$35$$35$46 () Bool (not (not (= a3 a0))))
(define-fun b$36$$35$$35$15 () Bool (<= a0 2147483647))
(define-fun b$36$$35$$35$21 () Bool (< a1 a2))
(define-fun b$36$$35$$35$23 () Bool (< (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0))
(define-fun b$36$$35$$35$25 () Bool (>= a3 (- 2147483648)))
(define-fun b$36$$35$$35$26 () Bool (<= a3 2147483647))
(define-fun b$36$$35$$35$27 () Bool (not (= a3 a0)))
(define-fun b$36$$35$$35$28 () Bool (not (< a3 a0)))
(define-fun b$36$$35$$35$29 () Bool (< a3 a0))
(define-fun b$36$$35$$35$30 () Bool (not (not (= a3 a0))))
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> 0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< 0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= 0 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< 0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= 0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 (- reftgen$36$n$36$0 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 (- reftgen$36$n$36$0 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> 0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= 0 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= 0 (- a0 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= 0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= reftgen$36$n$36$0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< reftgen$36$n$36$0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> reftgen$36$n$36$0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= reftgen$36$n$36$0 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= reftgen$36$n$36$0 (- reftgen$36$n$36$0 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< reftgen$36$n$36$0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= reftgen$36$n$36$0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= reftgen$36$n$36$0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= reftgen$36$n$36$0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= reftgen$36$n$36$0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= reftgen$36$n$36$0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< reftgen$36$n$36$0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= reftgen$36$n$36$0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= reftgen$36$n$36$0 (- a0 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> reftgen$36$n$36$0 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= reftgen$36$n$36$0 a0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (> reftgen$36$n$36$0 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (= a2 reftgen$36$n$36$0) (>= a2 reftgen$36$n$36$0) (<= a1 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0) (= a1 0)) b$36$$35$$35$40 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$28))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a1 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= a1 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a1 (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a1 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= a1 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (= a2 reftgen$36$n$36$0) (>= a2 reftgen$36$n$36$0) (<= a1 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0) (= a1 0)) b$36$$35$$35$41 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$28))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (<= a1 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0) (= a1 0)) b$36$$35$$35$12 b$36$$35$$35$44 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$29))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) a2)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$45 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$29))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a2 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= a2 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$40 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$28))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= a1 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a1 (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= a1 reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$41 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$28))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$44 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$29))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) a2)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$35 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (- a2 a1) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$36 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (- a2 a1) 18446744073709551615)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 18446744073709551615)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) reftgen$36$n$36$0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$42 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$29))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (>= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$43 b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$27 b$36$$35$$35$29))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (<= (+ (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2)) 1) 18446744073709551615)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert (and (and (exists ((fix$36$_$36$$35$15$35$$35$15 Int)) (and (not (not (= a3 a0))) (= a4 (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2))) (= reftgen$36$n$36$0 reftgen$36$n$36$0) (= a0 a0) (= a1 a1) (= a2 a2) (= a3 a3))) (exists ((fix$36$_$36$$35$15$35$$35$15 Int)) (and (not (not (= a3 a0))) (= a4 (+ a1 (SMTLIB_OP_DIV (- a2 a1) 2))) (= reftgen$36$n$36$0 reftgen$36$n$36$0) (= a0 a0) (= a1 a1) (= a2 a2) (= a3 a3))) (<= a2 reftgen$36$n$36$0) (>= a2 0) (>= a1 0) (<= a1 a2) (<= a1 reftgen$36$n$36$0)) b$36$$35$$35$12 b$36$$35$$35$13 b$36$$35$$35$14 b$36$$35$$35$15 b$36$$35$$35$21 b$36$$35$$35$23 b$36$$35$$35$25 b$36$$35$$35$26 b$36$$35$$35$30))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< a4 reftgen$36$n$36$0)))
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

