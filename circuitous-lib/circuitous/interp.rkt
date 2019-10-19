#lang racket/base

(provide unsat? verify-same assert-same execute)

(require
  "private/sem-sig.rkt"
  "private/interp-sig.rkt"
  "private/interp-unit.rkt"
  "private/three-valued-unit.rkt"
  "private/pos-neg-unit.rkt"
  "private/shared.rkt"
  "private/data.rkt"
  "private/contract.rkt"
  racket/unit
  racket/list
  (only-in rosette unsat?)
  racket/match
  racket/pretty)

(define-values/invoke-unit/infer
    (export (prefix pos-neg: interp^))
    (link interp@ pos-neg@))
(define-values/invoke-unit/infer
    (export (prefix three-valued: interp^))
    (link interp@ three-valued@))

(define (execute P . inputs)
  (if (constructive-circuit? P)
      (three-valued:eval/multi*
       inputs
       (circuit-term P)
       (circuit-reg-pairs P))
      (pos-neg:eval/multi*
       inputs
       (circuit-term P)
       (circuit-reg-pairs P))))

(define (verify-same P1 P2 #:constraints [constraints `true])
  (define register-pairs1 (circuit-reg-pairs P1))
  (define register-pairs2 (circuit-reg-pairs P2))
  (define outputs (remove-duplicates (append (circuit-outputs P1) (circuit-outputs P2))))
  (if (constructive-circuit? P1)
      (three-valued:verify-same P1 P2
                                #:register-pairs1 register-pairs1
                                #:register-pairs2 register-pairs2
                                #:constraints constraints
                                #:outputs outputs)
      (pos-neg:verify-same P1 P2
                           #:register-pairs1 register-pairs1
                           #:register-pairs2 register-pairs2
                           #:constraints constraints
                           #:outputs outputs)))

(define (pos-neg? p)
  (ormap (lambda (x) (list? (first x)))
         p))

(define (assert-same p q #:constraints [constraints `true])
  (define outputs
    (remove-duplicates (append (circuit-outputs p)
                               (circuit-outputs q))))
  (define x
    (verify-same p q
                 #:constraints constraints
                 #:register-pairs1 (circuit-reg-pairs p)
                 #:register-pairs2 (circuit-reg-pairs q)
                 #:outputs outputs))
  (unless (unsat? x)
    (match-define (list sat p1 q1) x)
    (define the-diff
      (for*/list ([l (in-list p1)]
                  [r (in-list q1)]
                  #:when (and (equal? (first l) (first r))
                              (not (equal? (second l) (second r)))))
        (list l r)))
    (error 'assert-same
           "rosette model gave counterexample:\n~a\n~a\n~a\n~a"
           (pretty-format sat)
           (pretty-format the-diff)
           (pretty-format p1)
           (pretty-format q1))))