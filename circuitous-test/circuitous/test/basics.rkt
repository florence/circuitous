#lang racket
(require rackunit
         circuitous
         (only-in circuitous/private/data
                  circuit-term
                  circuit-reg-pairs))
(test-case "contracts"
  (check-pred
   constructive-circuit?
   (make-circuit
    #:inputs '(a) #:outputs '(c)
    (a = b) (b = c)))
  (check-pred
   constructive-circuit?
   (make-circuit
    #:inputs '(a) #:outputs '(c)
    (a = c)))
  (check-pred
   classical-circuit?
   (constructive->classical
    (make-circuit
     #:inputs '(a) #:outputs '(c)
     (a = c)))))

(test-case "verification"
  (check-pred
   list?
   (verify-same
    (make-circuit
     #:inputs '(x)
     #:outputs '(z)
     (z = (and x a))
     (a = (or x a)))
    (make-circuit
     #:inputs '(x)
     #:outputs '(z)
     (z = x))))
  (check-pred
   list?
   (verify-same
    (make-circuit
     #:inputs '(b) #:outputs '(a)
     (a = b))
    (make-circuit
     #:inputs '(b) #:outputs '(a)
     (a = true)))))
(test-case "execute"
  (check-equal?
   (execute
    (make-circuit
     #:inputs '(b) #:outputs '(a)
     (a = b))
    '((b true)))
   (list (list '(b = true) '(a = true)))))
(test-case "constructive->classical"
  (check-pred
   classical-circuit?
   (constructive->classical
    (make-circuit
     #:inputs '(x)
     #:outputs '(z)
     (z = (and x a))
     (a = (or x a)))))
  (check-pred
   list?
   (verify-same
    (constructive->classical
     (make-circuit
      #:inputs '(x)
      #:outputs '(z)
      (z = (and x a))
      (a = (or x a))))
    (constructive->classical
     (make-circuit
      #:inputs '(x)
      #:outputs '(z)
      (z = x)))))
  (check-pred
   classical-circuit?
   (constructive->classical
    (make-circuit
     #:inputs '(c) #:outputs '(a)
     (a = c))))
  #;(execute
   (constructive->classical
    (make-circuit
     #:inputs '(c) #:outputs '(a)
     (a = c)))
   '(((+ c) true) ((- c) false))))
