#lang rosette/safe
(provide three-valued@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match
         (only-in racket/format ~a))

(define-unit three-valued@
  (import)
  (export sem^)
  (define (get-maximal-statespace x)
    (add1 (expt 2 x)))
  (define (initialize-to-false i)
    (map (lambda (x) (list x #f)) i))
  (define (f-or x y)
    (lambda (w)
      (define a (x w))
      (define b (y w))
      (case a
        [(#t) #t]
        [(#f) b]
        [else
         (case b
           [(#t) #t]
           [else '⊥])])))

  (define (f-and x y)
    (lambda (w)
      (define a (x w))
      (define b (y w))
      (case a
        [(#f) #f]
        [(#t) b]
        [else
         (case b
           [(#f) #f]
           [else '⊥])])))

  (define (f-not a)
    (lambda (w)
      (case (a w)
        [(#t) #f]
        [(#f) #t]
        [(⊥) '⊥])))
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
    (andmap
     (lambda (w)
       (match-define (list n a) w)
       (or (equal? a #t) (equal? a #f)))
     a)))
