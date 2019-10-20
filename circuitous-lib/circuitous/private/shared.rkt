#lang rosette/safe
(provide
 outputs=? deref contains?
 next-unique!)
(require (only-in racket/base error make-hasheq hash-ref hash-set! box set-box!)
         racket/match)


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
       a)))

(define (deref t v)
  (define x (assoc v t))
  (if x
      (second x)
      (error 'deref "~a is not in ~a" v t)))
(define (contains? t v)
  (not (false? (assoc v t))))

(require (only-in racket/base make-hash hash-update! hash-ref))
(define counter (make-hash))
(define (next-unique! x)
  (hash-update! counter x add1 (lambda () -1))
  (hash-ref counter x))