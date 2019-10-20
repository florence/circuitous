#lang racket/base
(provide (struct-out circuit)
         variable<?
         circuit-domain)
(require racket/match
         racket/list)
(struct circuit (outputs inputs reg-pairs term)
  #:transparent
  #:constructor-name a-circuit)
(define (circuit-domain c)
  (map first (circuit-term c)))
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