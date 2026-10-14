; FAIL
#lang typed/racket

(define (f x y)
    (set! y x)
    (if (number? y)
        (+ y 1) ; ERROR: y: Any
        0))
