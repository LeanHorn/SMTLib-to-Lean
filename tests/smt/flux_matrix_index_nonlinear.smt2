; ----------------------------------------------------------------------------
; flux_matrix_index_nonlinear.smt2  --  Flux
; ----------------------------------------------------------------------------
; Rust     :
;     /// Row-major matrix indexing: the bound check is nonlinear.
;     #[spec(fn(m: &[f32][@len], rows: usize, cols: usize, i: usize{i < rows}, j: usize{j < cols}) -> f32
;            requires len == rows * cols)]
;     pub fn get(m: &[f32], rows: usize, cols: usize, i: usize, j: usize) -> f32 {
;         m[i * cols + j]
;     }
; Shows    : row-major index bound i*cols + j < rows*cols; multiplication of
;            two variables goes through SMTLIB_OP_MUL (nonlinear).
; Theories : NIA
; Produced : cargo flux (dump_constraint = true) -> log/fluxq.get.smt2 (fixpoint
;            horn), then fixpoint --save --allowho --allowhoqs --solver=z3
;            (the flags Flux itself passes to fixpoint).
; Body     : the verbatim z3 session fixpoint saved to .liquid/<input>.smt2.
;            Each (check-sat) is followed by fixpoint's `; SMT Says:` comment
;            recording z3's answer. 1 check-sat: 1 unsat, 0 sat.
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
(declare-fun fix$36$_$36$$35$6 () Int)
(declare-fun ge () Int)
(declare-fun reftgen$36$cols$36$2 () Int)
(declare-fun cast_as () Int)
(declare-fun reftgen$36$len$36$0 () Int)
(declare-fun gt () Int)
(declare-fun fix$36$_$36$$35$1 () Int)
(declare-fun reftgen$36$j$36$4 () Int)
(declare-fun fix$36$_$36$$35$2 () Int)
(declare-fun fix$36$_$36$$35$5 () Int)
(declare-fun fix$36$_$36$$35$7$35$$35$1 () Int)
(declare-fun lt () Int)
(declare-fun reftgen$36$rows$36$1 () Int)
(declare-fun fix$36$_$36$$35$7 () Int)
(declare-fun reftgen$36$i$36$3 () Int)
(declare-fun fix$36$_$36$ () Int)
(declare-fun fix$36$_$36$$35$3 () Int)
(declare-fun cast_as_int () Int)
(declare-fun fix$36$_$36$$35$4 () Int)
; solve: start

; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
(define-fun b$36$$35$$35$5 () Bool (= reftgen$36$len$36$0 (SMTLIB_OP_MUL reftgen$36$rows$36$1 reftgen$36$cols$36$2)))
(define-fun b$36$$35$$35$6 () Bool (< reftgen$36$i$36$3 reftgen$36$rows$36$1))
(define-fun b$36$$35$$35$7 () Bool (< reftgen$36$j$36$4 reftgen$36$cols$36$2))
(define-fun b$36$$35$$35$8 () Bool (>= reftgen$36$len$36$0 0))
(define-fun b$36$$35$$35$9 () Bool (>= reftgen$36$rows$36$1 0))
(define-fun b$36$$35$$35$10 () Bool (>= reftgen$36$cols$36$2 0))
(define-fun b$36$$35$$35$11 () Bool (>= reftgen$36$i$36$3 0))
(define-fun b$36$$35$$35$12 () Bool (>= reftgen$36$j$36$4 0))
(define-fun b$36$$35$$35$13 () Bool (>= reftgen$36$j$36$4 0))
; smtBracket - start: sendConcreteBindingsToSMT

(push 1)
; smtBracket - start: filterValidLHS

(push 1)
(assert (and true b$36$$35$$35$5 b$36$$35$$35$6 b$36$$35$$35$7 b$36$$35$$35$8 b$36$$35$$35$9 b$36$$35$$35$10 b$36$$35$$35$11 b$36$$35$$35$12 b$36$$35$$35$13))
; smtBracket - start: filterValidRHS

(push 1)
(assert (not (< (+ (SMTLIB_OP_MUL reftgen$36$i$36$3 reftgen$36$cols$36$2) reftgen$36$j$36$4) reftgen$36$len$36$0)))
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

