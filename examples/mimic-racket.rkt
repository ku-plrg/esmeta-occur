#lang typed/racket

(define-type ESValue Any) (define-type Object String) (define-type Completion (Pair String Any))
(define: (LengthOfArrayLike [obj : Object]): Any "")
(define: (IsArray [argument : ESValue]): Completion ; No type propositions for completion records
  (cond
    [(not (string? argument)) (cons "Normal" #f)]
    [(random) (cons "Throw" "Error")]
    [else (cons "Normal" #t)]))
(define: (FlattenIntoArray [element : ESValue]): Any
  (let ([shouldFlatten (IsArray element)])
    (if (and (equal? (car shouldFlatten) "Normal") (cdr shouldFlatten))
        (LengthOfArrayLike element) ""))) ; `element` should be `Object` but `ESValue`
