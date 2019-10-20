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
  (expect-failure
   (rename id '(I1 I2)))
  (check-equal?
   (rename id '(I1 I2)
           #:constraints '(or (and I1 I2) (and (not I1) (not I2))))
   (circuit
    #:inputs (I2 I3)
    #:outputs (O1 O2 O3)
    (O1 = I2)
    (O2 = I2)
    (O3 = I3))))

(test-case "1"
  (define one
    (circuit
     #:inputs ()
     #:outputs (one)
     (one = true)))
  (check-equal?
   (replace one `(true (or true false)))
   (circuit
     #:inputs ()
     #:outputs (one)
     (one = (or #t false)))))

(test-case "link with example safe esterel context"
  (define safe-context
    (circuit
      #:inputs (GO KILL SUSP RES in-sel)
      #:outputs (SEL K0 K1)
      (SEL = in-sel)
      (safe-go = (and GO (not SEL)))))
  (define (safe l)
    (link
     safe-context
     #:with l
     #:inputs '((GO safe-go) (KILL KILL) (SUSP SUSP) (RES RES))
     #:outputs '((SEL safe-sel) (K0 K0) (K1 K1))))
  (define pause
    (circuit
     #:inputs (GO RES SUSP KILL)
     #:outputs (K0 K1 SEL)
     (reg in SEL = (and (not KILL) do-sel))
     (K0 = (and SEL RES))
     (K1 = GO)
     (do-sel = (or GO do-susp))
     (do-susp = (and SUSP SEL))))
  (check-pred
   unsat?
   (verify-same
    #:constraints '(implies SEL (not GO))
    pause
    (safe pause))))
     
     