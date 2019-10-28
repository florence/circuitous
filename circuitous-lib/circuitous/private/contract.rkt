#lang racket/base
(provide
 equations?
 constructive-circuit?
 classical-circuit?
 same-circuit-as/c
 variable/c
 boolean-expression/c
 extended-boolean-expression/c
 distinct?
 FV)
(require "redex.rkt" "data.rkt"
         redex/reduction-semantics
         racket/contract
         racket/set
         racket/match)

(module+ test (require rackunit))

(define (equations? P)
  (redex-match? constructive P P))

(define (constructive-circuit? P)
  (redex-match? constructive P (circuit-term P)))
(define (classical-circuit? P)
  (redex-match? classical P (circuit-term P)))
(define (same-circuit-as/c a)
  (cond [(constructive-circuit? a) constructive-circuit?]
        [(classical-circuit? a) classical-circuit?]
        [else (error "malformed circuit while checking for circuit type")]))

(define variable/c
  (flat-named-contract
   "variable/c"
   (or/c symbol?
         (list/c '+ symbol?)
         (list/c '- symbol?))))

(define (make-boolean-expression/c x name)
  (define y
    (flat-named-contract
     name
     (recursive-contract
      (or/c variable/c
            (x y)
            #f #t
            (list/c 'and y y)
            (list/c 'or y y)
            (list/c 'not y))
      #:flat)))
  y)

(define boolean-expression/c
  (make-boolean-expression/c (lambda (_) none/c) "boolean-expression/c"))
(define extended-boolean-expression/c
  (make-boolean-expression/c
   (lambda (x)
     (list/c 'implies x x))
   "extended-boolean-expression/c"))

(define (distinct? a b)
  (equal? (set) (set-intersect (list->set a) (list->set b))))

(define (FV x)
  (match x
    [(or 'true 'false #t #f '⊥) (set)]
    [(list (or 'and 'or 'implies) a b)
     (set-union (FV a) (FV b))]
    [(list 'not a)
     (FV a)]
    [(or (? symbol? a)
         (and a (list (or '+ '-) _)))
     (set a)]))

(module+ test
  (check-equal?
   (FV '(implies (+ SEL) (- GO)))
   (set '(+ SEL) '(- GO)))
  (check-equal?
   (FV '(and (+ SEL) (- GO)))
   (set '(+ SEL) '(- GO)))
  (check-equal?
   (FV '(or (+ SEL) (- GO)))
   (set '(+ SEL) '(- GO)))
  (check-equal?
   (FV '(implies true (- GO)))
   (set '(- GO)))
  (check-equal?
   (FV '(implies false (- GO)))
   (set '(- GO)))
  (check-equal?
   (FV '(implies #f (- GO)))
   (set '(- GO)))
  (check-equal?
   (FV '(implies #t (- GO)))
   (set '(- GO)))
  (check-equal?
   (FV '(implies ⊥ (- GO)))
   (set '(- GO)))
  (check-equal?
   (FV '(not (- GO)))
   (set '(- GO))))