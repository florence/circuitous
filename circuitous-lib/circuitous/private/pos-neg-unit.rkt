#lang rosette/safe
(provide pos-neg@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match
         (only-in racket/format ~a)
         (only-in racket/string string-replace)
         (only-in racket/base error))

(define-unit pos-neg@
  (import)
  (export sem^)
  (define (interp-bound formula)
    (define y (plus-and-minus formula))
    ;; for anything that has a +/- part
    ;; only one can change so we don't need to
    ;; double count in the execution bound
    (+ y (- (length formula) (* 2 y))))
  
  (define (plus-and-minus y)
    (cond [(empty? y) 0]
          [(list? (first (first y)))
           (define name (first (first y)))
           (define other (if (eq? (first name) '+) '- '+))
           (if (assoc (list other (second name)) y)
               (add1 (plus-and-minus (rest y)))
               (plus-and-minus (rest y)))]
          [else (plus-and-minus (rest y))]))
  
  (define (get-maximal-statespace x)
    (expt 2 (inexact->exact (ceiling (/ x 2)))))
  (define (initialize-to-false i)
    (map (lambda (x)
           (if (and (list? x)
                    (equal? '- (first x)))
               (list x #t)
               (list x #f)))
         i))
  (define initial-value #f)
  (define (f-or a b)
    (lambda (w)
      (or/force (a w) (b w))))
  (define (f-and a b)
    (lambda (w)
      (and/force (a w) (b w))))
  (define (f-not n)
    (lambda (w)
      (not/force (n w))))
  (define (and/force a b)
    (if (and (boolean? a) (boolean? b))
        (and a b)
        (error "not boolean")))
  (define (or/force a b)
    (if (and (boolean? a) (boolean? b))
        (or a b)
        (error "not boolean")))
  (define (not/force a)
    (if (boolean? a)
        (not a)
        (error "not boolean")))
  (define (f-implies a b)
    (lambda (w)
      (implies (a w) (b w))))
  (define (symbolic-boolean name)
    (constant (string-replace
               (~a name "$" (next-unique! name))
               " "
               "_")
              boolean?))
  (define (constraints I)
    (andmap
     (λ (x)
       (implies
        (and (list? x)
             (list? (first x))
             (eq? (first (first x)) '+)
             (contains? I `(- ,(second (first x)))))
        (not (and (second x)
                  (deref I `(- ,(second (first x))))))))
     I))
  (define (constructive? P)
    (andmap
     (lambda (x)
       (implies 
        (and (list? x)
             (list? (first x))
             (eq? (first (first x)) '+)
             (contains? P `(- ,(second (first x)))))
        (or (second x)
            (deref P `(- ,(second (first x)))))))
     P))

  (define (outputs=? a b #:outputs [outputs #f])
  (if outputs
      (andmap
       (lambda (w)
         (cond
           [(and (list? w) (equal? (first w) '-))
            (equal?
             (or (not (contains? a w)) (deref a w))
             (or (not (contains? b w)) (deref b w)))]
           [else
            (equal?
             (and (contains? a w) (deref a w))
             (and (contains? b w) (deref b w)))]))
       outputs)
      (andmap
       (lambda (w)
         (implies
          (contains? b (first w))
          (equal? (second w) (deref b (first w)))))
       a))))