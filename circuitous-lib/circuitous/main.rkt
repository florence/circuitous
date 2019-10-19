#lang rosette/safe

(provide unsat? verify-same)

(require
  "private/sem-sig.rkt"
  "private/interp-sig.rkt"
  "private/interp-unit.rkt"
  "private/three-valued-unit.rkt"
  "private/pos-neg-unit.rkt"
  "private/shared.rkt"
  racket/unit)

(define-values/invoke-unit/infer
    (export (prefix pos-neg: interp^))
    (link interp@ pos-neg@))
(define-values/invoke-unit/infer
    (export (prefix three-valued: interp^))
    (link interp@ three-valued@))


(define (verify-same P1 P2
                     #:register-pairs1 [register-pairs1 #f]
                     #:register-pairs2 [register-pairs2 #f]
                     #:constraints [constraints `true]
                     #:outputs [outputs #f])
  (if (pos-neg? P1)
      (pos-neg:verify-same P1 P2
                           #:register-pairs1 register-pairs1
                           #:register-pairs2 register-pairs2
                           #:constraints constraints
                           #:outputs outputs)
      (three-valued:verify-same P1 P2
                                #:register-pairs1 register-pairs1
                                #:register-pairs2 register-pairs2
                                #:constraints constraints
                                #:outputs outputs)))

(define (pos-neg? p)
  (ormap (lambda (x) (list? (first x)))
         p))