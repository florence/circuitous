#lang rosette/safe
(provide deref contains?
 next-unique!)
(require (only-in racket/base error make-hasheq hash-ref hash-set! box set-box!)
         racket/match)

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