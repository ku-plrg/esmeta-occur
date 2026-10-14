; PASS
#lang typed/racket

(define (g x)
  (let [(y (number? x))]
    (if y
        (+ x 1)
        0)))
