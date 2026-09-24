; ----------------------------------------------------------------------------
; flux_bitvec_page_align.smt2  --  Flux
; ----------------------------------------------------------------------------
; Rust     :
;     /// Bitvector reasoning: masking to a 4 KiB page boundary.
;     #[spec(fn(x: BV32) -> BV32{v: bv_ule(v, x) && bv_and(v, bv_int_to_bv32(4095)) == bv_int_to_bv32(0)})]
;     pub fn page_align_down(x: BV32) -> BV32 {
;         x & 0xFFFF_F000u32
;     }
; Shows    : Flux BV32 refinements: bvand / bvule / int2bv.
; Theories : BV (+ int2bv)
; Produced : cargo flux (dump_constraint = true) -> log/fluxq.page_align_down.smt2 (fixpoint
;            horn), then fixpoint --save --allowho --allowhoqs --solver=z3
;            (the flags Flux itself passes to fixpoint).
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 2 check-sat: 2 unsat, 0 sat.
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
(declare-fun ge () Int)
(declare-fun cast_as () Int)
(declare-fun gt () Int)
(declare-fun reftgen$36$x$36$0$35$$35$1 () (_ BitVec 32))
(declare-fun lt () Int)
(declare-fun reftgen$36$x$36$0$35$$35$2 () (_ BitVec 32))
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
(assert (not (bvule (bvand reftgen$36$x$36$0$35$$35$1 ((_ int2bv 32) 4294963200)) reftgen$36$x$36$0$35$$35$1)))
(check-sat)
; SMT Says: Unsat
(pop 1)
; smtBracket - end: filterValidRHS

(pop 1)
; smtBracket - end: filterValidLHS

; smtBracket - start: filterValidLHS

(push 1)
(assert true)
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (= (bvand (bvand reftgen$36$x$36$0$35$$35$2 ((_ int2bv 32) 4294963200)) ((_ int2bv 32) 4095)) ((_ int2bv 32) 0))))
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

