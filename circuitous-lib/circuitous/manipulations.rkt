#lang racket/base
(provide make-circuit
         link
         propigate&remove
         propigate
         rename
         replace
         circuit->classical)
         
(require racket/contract)
(require redex/reduction-semantics
         racket/list
         (for-syntax syntax/parse racket/base
                     racket/list)
         "private/redex.rkt"
         "private/data.rkt"
         "interp.rkt")

(module+ test (require rackunit))

(begin-for-syntax
  (define-syntax-class bool-equation
    #:datum-literals (=)
    #:attributes (splice-term reg-pairs lhs)
    (pattern (a:id = b:bool-expr)
             #:attr splice-term
             #''((a = b))
             #:attr reg-pairs #''()
             #:attr lhs #'a)
    (pattern (reg in:id out:id = b:bool-expr)
             #:attr splice-term
             #''((in = b))
             #:attr reg-pairs
             #''((in out))
             #:attr lhs #'in))
  (define-syntax-class bool-expr
    #:datum-literals (and or not true false ⊥ reg)
    (pattern name:id)
    (pattern true)
    (pattern false)
    (pattern ⊥)
    (pattern (and a:bool-expr b:bool-expr))
    (pattern (or a:bool-expr b:bool-expr))
    (pattern (not a:bool-expr))
    (pattern (reg in:id out:id))))

(define-syntax make-circuit
  (syntax-parser
    [(_ (~alt (~once (~seq #:inputs inputs))
              (~once (~seq #:outputs outputs)))
        ...
        p:bool-equation ...)
     #:fail-when (not (equal? (syntax->datum #'(p.lhs ...))
                              (remove-duplicates (syntax->datum #'(p.lhs ...)))))
     "duplicate wire name"
     #'(apply make-circuitf
              #:inputs inputs
              #:outputs outputs
              (equations p ...))]))

(define (make-circuitf #:inputs inputs
                       #:outputs outputs
                       reg-pairs
                       . expr)
  (circuit inputs outputs expr))

(define-syntax equations
  (syntax-parser
    [(_ r:bool-equation ...)
     #'(list
        (append r.reg-pairs ...)
        (append r.splice-term ...))]))

(define (link a
              #:with b
              #:inputs inputs
              #:outputs outputs)
  (define x
    (term (rename*/freshen
           ,(circuit-reg-pairs b)
           ,(circuit-term b)
           ,@inputs
           ,@outputs
           ,(circuit-term a))))
  (apply
   make-circuitf
   #:inputs (circuit-inputs a)
   #:outputs (circuit-outputs a)
   (append (circuit-reg-pairs a) (first x))
   (append
    (circuit-term a)
    (second x))))

(define (propigate&remove P . a)
  (apply
   make-circuitf
   #:inputs (remove* a (circuit-inputs P))
   #:outputs (remove* a (circuit-outputs P))
   (remf (lambda (x)
           (or (member (first x) a)
               (member (second x) a)))
         (circuit-reg-pairs P))
   (term (propigate/remove*
          ,(circuit-term P)
          ,@a))))
(define (propigate P . a)
  (apply
   make-circuitf
   #:inputs (circuit-inputs P)
   #:outputs (circuit-outputs P)
   (circuit-reg-pairs P)
   (term (propigate*
          ,(circuit-term P)
          ,@a))))
(define (rename P . a)
  (apply
   make-circuitf
   #:inputs (term (replace-p* ,(circuit-inputs P) ,@a))
   #:outputs (term (replace-p* ,(circuit-outputs P) ,@a))
   (flatten (circuit-reg-pairs P))
   (term (rename** ,(circuit-term P) ,@a))))

(define (replace P . ps)
  (apply
   (make-circuitf
    #:inputs (circuit-inputs P)
    #:outputs (circuit-outputs P)
    (circuit-reg-pairs P)
    (term (replace* P ,@ps)))))

(define (circuit->classical P)
  (define (convert-names x)
    (append-map (lambda (x) (list `(+ ,x) `(- ,x))) x))
  (apply
   (make-circuitf
    #:inputs (convert-names (circuit-inputs P))
    #:outputs (convert-names (circuit-outputs P))
    (append-map
     (lambda (x)
       (list (list `(+ ,(first x)) `(+ ,(first x)))
             (list `(- ,(first x)) `(- ,(first x)))))
     (circuit-reg-pairs P))
    (term (convert-P ,P)))))
    
