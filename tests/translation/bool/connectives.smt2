; One satisfiable query covering declarations, names, metadata, and connectives.
(set-info :smt-lib-version 2.6)
(set-info :source |A Boolean example; (check-sat) here is just text.|)
(set-info :category "crafted")
(set-info :license "MIT")
(set-info :notes "A doubled quote: ""hello""")
(set-info :status sat)
(set-logic QF_UF)

; Both declaration forms, quoted names, and an unused declaration.
(declare-const |True| Bool)
(declare-fun |a b| () Bool)
(declare-const p Bool)
(declare-fun q () Bool)
(declare-const r Bool)
(declare-const unused Bool)

; |True| is a variable, distinct from the literal true.
(assert |True|)
(assert (= |True| |a b|))
(assert true)
(assert (not false))
(assert (and p q r))
(assert (or (not p) q r))
(assert (=> p q r))
(assert (= p q r))
(assert (= |a b| p))
; xor means odd parity, including when all three operands are true.
(assert (xor p (not q)))
(assert (xor p q r))
(assert (not (xor p q r true)))
; Bool distinct compares every pair; three Boolean values cannot all differ.
(assert (distinct p false))
(assert (not (distinct p q r)))
(check-sat)
(set-info :status unknown)
(exit)
