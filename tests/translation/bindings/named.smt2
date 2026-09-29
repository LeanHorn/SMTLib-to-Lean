; Names are aliases for their bodies, not extra query parameters.
(set-logic UFLIA)
(declare-const x Int)
(declare-const p Bool)
(define-fun next () Int (+ x 1))
(assert (! (> next 0) :named positive))
(assert (not positive))
; cvc5 keeps only one of these labels in getNamedTerms; preserve both sources.
(assert (! (> next 0) :named |same body|))
; Nested names are usable later in the same command.
(assert (and (! (= x 1) :named |left (;):named|)
             (! |left (;):named| :named right) right))
; A later binder with the same name must not capture a named body's global x.
(assert (let ((saved positive))
  (forall ((x Int) (p Bool)) (= saved positive))))
; Named Int subterms also retain their definition, including prior define-fun.
(assert (and (= (! next :named |next value|) next) (= |next value| (+ x 1))))
; Multiple labels and embedded newlines must remain safe in Lean comments.
(assert (and (! p :named |line
name| :named also) |line
name| also))
(check-sat)
