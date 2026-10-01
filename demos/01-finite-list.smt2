; Can a finite list be its own tail? Expected: unsat.
; Showcase: recursive datatypes, constructor injectivity, and a Lean induction proof.
(set-logic ALL)
(declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
(declare-const xs IntList)
(declare-const x Int)
(assert (= xs (cons x xs)))
(check-sat)
