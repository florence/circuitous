#lang racket
(require rackunit
         circuitous
         threading
         (for-syntax syntax/parse))

(define-syntax expect-failure
  (syntax-parser
    [(_ a)
     (syntax/loc this-syntax
       (check-exn
        #rx"assert-same.*model"
        (lambda () a)))]))

(test-case "Identity Circuit"
  (define id
    (circuit
     #:inputs (I1 I2 I3)
     #:outputs (O1 O2 O3)
     (O1 = I1)
     (O2 = I2)
     (O3 = I3)))
  (check-equal?
   (propagate id 'O2 'O1)
   id)
  (expect-failure
   (propagate&remove id 'O2 'O1))
  (check-equal?
   (propagate&remove
    id 'O2 'O1
    #:constraints
    '(and (not O1) (not O2)))
   (circuit
    #:inputs (I1 I2 I3)
    #:outputs (O3)
    (O3 = I3)))
  (check-equal?
   (propagate&remove
    id 'O2 'O1
    #:constraints 'false)
   (circuit
    #:inputs (I1 I2 I3)
    #:outputs (O3)
    (O3 = I3)))
  (check-equal?
   (propagate&remove
    id 'O2 'O1
    #:constraints #f)
   (circuit
    #:inputs (I1 I2 I3)
    #:outputs (O3)
    (O3 = I3)))
  (expect-failure
   (replace id '(I1 I2)))
  (check-equal?
   (replace id '(I1 I2)
            #:constraints '(or (and I1 I2) (and (not I1) (not I2))))
   (circuit
    #:inputs (I1 I2 I3)
    #:outputs (O1 O2 O3)
    (O1 = I2)
    (O2 = I2)
    (O3 = I3)))   
   
  )