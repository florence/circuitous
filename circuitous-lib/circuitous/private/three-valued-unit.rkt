#lang rosette/safe
(provide three-valued@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match
         (only-in racket/format ~a)
         (only-in racket/base error))

(define-unit three-valued@
  (import interp^)
  (export sem^)
  (define (interp-bound formula)
    (length formula))
  (define initial-value '⊥)
  (define (get-maximal-statespace x)
    (expt 2 x))
  (define (initialize-to-false i)
    (map (lambda (x) (list x #f)) i))
  (define (f-or x y)
    (lambda (w)
      (define a (x w))
      (define b (y w))
      (case a
        [(#t) #t]
        [(#f) b]
        [(⊥)
         (case b
           [(#t) #t]
           [(#f ⊥) '⊥]
           [else (error 'or "second argument is not an extended boolean: ~a" b)])]
        [else
         (error 'or "first argument is not an extended boolean: ~a" a)])))

  (define (f-and x y)
    (lambda (w)
      (define a (x w))
      (define b (y w))
      (case a
        [(#f) #f]
        [(#t) b]
        [(⊥)
         (case b
           [(#f) #f]
           [(#t ⊥) '⊥]
           [else (error 'and "second argument is not an extended boolean: ~a" b)])]
        [else
         (error 'and "first argument is not an extended boolean: ~a" a)])))

  (define (f-not a)
    (lambda (w)
      (case (a w)
        [(#t) #f]
        [(#f) #t]
        [(⊥) '⊥]
        [else (error 'not "argument is not an extended boolean: ~a" (a w))])))
  ;; TODO: is this the right extention of constructive implies
  ;; to scott domains?
  (define (f-implies a b)
    (lambda (w)
      (case (a w)
        [(#t) (b w)]
        [(#f) #t]
        [(⊥) '⊥])))
  (define (symbolic-boolean name)
    (define pos
      (constant (~a "pos-" name "$" (next-unique! name)) boolean?))
    (define neg
      (constant (~a "neg-" name "$" (next-unique! name)) boolean?))
    (assert (not (and pos neg)))
    (if pos #t (if neg #f '⊥)))
  (define (constraints _)
    #t)
  (define (constructive? a)
    (equal?
     ((build-expression (constructive-constraints a)) a)
     #t))
  
  (define (constructive-constraints inputs)
    (if (empty? inputs)
        'true
        `(and (or ,(first (first inputs)) (not ,(first (first inputs))))
              ,(constructive-constraints (rest inputs)))))

  (define (outputs=? a b #:outputs [outputs #f])
  (if outputs
      (andmap
       (lambda (w)
         (equal?
          (and (contains? a w) (deref a w))
          (and (contains? b w) (deref b w))))
       outputs)
      (andmap
       (lambda (w)
         (implies
          (contains? b (first w))
          (equal? (second w) (deref b (first w)))))
       a))))
