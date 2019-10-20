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
     #:inputs '()
     #:outputs '(a) 
     (a = (and a a)))
    (make-circuit
     #:inputs '(b)
     #:outputs '(a) 
     (b = (and a a)))))
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
(test-case "construction"
  (check-equal?
   (circuit-reg-pairs
    (make-circuit
     #:inputs '(b) #:outputs '(a out)
     (a = b)
     (reg in out = a)))
   '((in out))))
(test-case "execute"
  (check-equal?
   (execute
    (make-circuit
     #:inputs '(a)
     #:outputs '(b) 
     (b = (and a a)))
    '((a true)))
   '(((a #t) (b #t))))
  (check-equal?
   (execute
    (make-circuit
     #:inputs '(a)
     #:outputs '(b) 
     (b = (and a a)))
    '((a #f)))
   '(((a #f) (b #f))))
  (check-equal?
   (execute
    (make-circuit
     #:inputs '(b) #:outputs '(a)
     (a = b))
    '((b true)))
   (list (list '(b #t) '(a #t))))
  (check-equal?
   (execute
    (make-circuit
     #:inputs '(b) #:outputs '(a out)
     (a = b)
     (reg in out = a))
    '((b true)) '((b false)) '((b false)))
   (list (list '(b #t) '(a #t)
               '(in #t) '(out #f))
         (list '(b #f) '(a #f)
               '(in #f) '(out #t))
         (list '(b #f) '(a #f)
               '(in #f) '(out #f)))))
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
  (check-equal?
   (execute
    (constructive->classical
     (make-circuit
      #:inputs '(c) #:outputs '(a)
      (a = c)))
    '(((+ c) true) ((- c) false)))
   (list (list '((+ c) #t) '((- c) #f)
               '((+ a) #t) '((- a) #f))))
  #;
  (check-equal?
   (execute
    (constructive->classical
     (make-circuit
      #:inputs '(b) #:outputs '(a out)
      (a = b)
      (reg in out = a))
     '((b true) (b false) (b false))))
   (list (list '(b true) '(a true)
               '(in true) '(out false))
         (list '(b false) '(a false)
               '(in false) '(out true))
         (list '(b false) '(a false)
               '(in false) '(out false)))))
