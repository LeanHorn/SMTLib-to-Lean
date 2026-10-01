; Can an unsigned binary-search midpoint escape its bounds? Expected: unsat.
; Showcase: actual 32-bit arithmetic and logical shifts, not unbounded integers.
; The naive (lo + hi) >> 1 can wrap; lo + ((hi - lo) >> 1) stays in range.
(set-logic QF_BV)
(declare-const lo (_ BitVec 32))
(declare-const hi (_ BitVec 32))
(define-fun midpoint () (_ BitVec 32)
  (bvadd lo (bvlshr (bvsub hi lo) #x00000001)))
(assert (bvule lo hi))
(assert (or (bvult midpoint lo) (bvugt midpoint hi)))
(check-sat)
