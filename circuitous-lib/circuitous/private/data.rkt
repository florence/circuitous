#lang racket/base
(provide (struct-out circuit)
         variable<?)
(require racket/match)
(struct circuit (outputs inputs reg-pairs term)
  #:transparent)
(define (variable<? x y)
  (match* (x y)
    [(`(+ ,x) `(+ ,y))
     (symbol<? x y)]
    [(`(- ,x) `(- ,y))
     (symbol<? x y)]
    [(`(+ ,x) `(- ,y))
     (or (equal? x y)
         (symbol<? x y))]
    [(`(- ,x) `(+ ,y))
     (if (equal? x y)
         #f
         (symbol<? x y))]
    [((? symbol?) (? list?))
     #f]
    [((? list?) (? symbol?))
     #t]
    [(_ _) (symbol<? x y)]))