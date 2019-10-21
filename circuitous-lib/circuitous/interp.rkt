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
  (only-in "private/redex.rkt" rename-internals)
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

(define-logger circuit-solver)
(define-logger circuit-eval)

(define (execute P . inputs*)
  (define inputs
    (for/list ([input (in-list inputs*)])
      (for/list ([i (in-list (sort input variable<? #:key first))])
        (list (first i)
              (if (symbol? (second i))
                  (eq? (second i) 'true)
                  (second i))))))
  (define evaluate
    (cond [(constructive-circuit? P)
           (log-circuit-eval-debug "evaling as a constructive circuit")
           three-valued:eval/multi*]
          [else
           (log-circuit-eval-debug "evaling as a classical circuit")
           pos-neg:eval/multi*]))
  (evaluate
   inputs
   (circuit-term P)
   (circuit-reg-pairs P)))

(define (verify-same P1 P2
                     #:constraints [constraints `true]
                     #:extra-outputs [extra-outputs empty])
  (define register-pairs1 (circuit-reg-pairs P1))
  (define register-pairs2 (circuit-reg-pairs P2))
  (define outputs
    (remove-duplicates (append extra-outputs (circuit-outputs P1) (circuit-outputs P2))))
  (define solve 
    (cond [(constructive-circuit? P1)
           (log-circuit-solver-debug "solving as a constructive circuit")
           three-valued:verify-same]
          [else
           (log-circuit-solver-debug "solving as a classical circuit")
           pos-neg:verify-same]))
  (define p1::p2
    (rename-internals
     (circuit-term P1)
     (circuit-term P2)
     #:c1-interface (append extra-outputs (circuit-inputs P1) (circuit-outputs P1))
     #:c2-interface (append extra-outputs (circuit-inputs P2)  (circuit-outputs P2))))
  (solve (first p1::p2) (second p1::p2)
         #:register-pairs1 register-pairs1
         #:register-pairs2 register-pairs2
         #:constraints constraints
         #:outputs outputs))

(define (assert-same p q
                     #:constraints [constraints `true]
                     #:extra-outputs [extra-outputs empty])
  (define x
    (verify-same p q
                 #:constraints constraints
                 #:extra-outputs empty))
  (unless (unsat? x)
    (match-define (list sat p1 q1) x)
    (define the-diff
      (for/list ([p1 (in-list p1)]
                 [q1 (in-list q1)])
        (for*/list ([l (in-list p1)]
                    [r (in-list q1)]
                    #:when (and (equal? (first l) (first r))
                                (not (equal? (second l) (second r)))))
          (list l r))))
    (error 'assert-same
           "rosette model gave counterexample:\n~a\n~a\n~a\n~a"
           (pretty-format sat)
           (pretty-format the-diff)
           (pretty-format p1)
           (pretty-format q1))))