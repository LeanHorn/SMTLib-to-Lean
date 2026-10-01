; Can a timestamp fall outside its computed one-millisecond bucket? Expected: unsat.
; Showcase: exact Real arithmetic, Int/Real conversions, and floor at negative times.
; For example, time = -0.0005 seconds belongs to bucket -1, not bucket 0.
(set-logic ALL)
(declare-const time Real)
(define-fun milliseconds () Real (* time 1000.0))
(define-fun bucket () Int (to_int milliseconds))
(assert (or (< milliseconds (to_real bucket))
            (>= milliseconds (+ (to_real bucket) 1.0))))
(check-sat)
