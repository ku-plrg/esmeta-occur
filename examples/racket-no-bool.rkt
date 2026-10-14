; FAIL
#lang typed/racket

(define (f x)
  (let [(y (if (number? x) "abc" 42))]
    (if (number? y)
        0
        (+ x 1)))) ; ERROR: x: Any
