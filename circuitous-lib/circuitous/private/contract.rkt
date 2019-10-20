#lang racket/base
(provide
 equations?
 constructive-circuit?
 classical-circuit?
 same-circuit-as/c
 variable/c
 boolean-expression/c
 extended-boolean-expression/c
 distinct?)
(require "redex.rkt" "data.rkt"
         redex/reduction-semantics
         racket/contract
         racket/set)

(define (equations? P)
  (redex-match? constructive P P))

(define (constructive-circuit? P)
  (redex-match? constructive P (circuit-term P)))
(define (classical-circuit? P)
  (redex-match? classical P (circuit-term P)))
(define (same-circuit-as/c a)
  (if (classical-circuit? a) classical-circuit? constructive-circuit?))

(define variable/c
  (flat-named-contract
   "variable/c"
   (or/c symbol?
         (list/c '+ symbol?)
         (list/c '- symbol?))))

(define (make-boolean-expression/c x)
  (define y
    (flat-named-contract
     "boolean-expression/c"
     (recursive-contract
      (or/c variable/c
            (x y)
            #f #t
            (list/c 'and boolean-expression/c boolean-expression/c)
            (list/c 'or boolean-expression/c boolean-expression/c)
            (list/c 'not boolean-expression/c))
      #:flat)))
  y)

(define boolean-expression/c (make-boolean-expression/c (lambda (_) none/c)))
(define extended-boolean-expression/c
  (make-boolean-expression/c
   (lambda (x)
     (list/c 'implies x x))))

(define (distinct? a b)
  (equal? (set) (set-intersect (list->set a) (list->set b))))