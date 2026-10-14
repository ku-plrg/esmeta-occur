; PASS
#lang typed/racket

(define (isNumber x) (number? x))

(define (g x)
  (if (isNumber x)
      (+ x 1)
      0))

