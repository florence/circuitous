#lang racket/base
(provide
 equations?
 constructive-circuit?
 classical-circuit?
 same-circuit-as/c
 variable/c
 boolean-expression/c)
(require "redex.rkt" "data.rkt"
         redex/reduction-semantics
         racket/contract)

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

(define boolean-expression/c
  (flat-named-contract
   "boolean-expression/c"
   (recursive-contract
    (or/c variable/c
          (list/c 'and boolean-expression/c boolean-expression/c)
          (list/c 'or boolean-expression/c boolean-expression/c)
          (list/c 'not boolean-expression/c))
    #:flat)))