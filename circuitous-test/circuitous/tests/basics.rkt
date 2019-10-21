#lang racket
(require rackunit
         circuitous
         circuitous/private/redex
         redex/reduction-semantics
         (only-in circuitous/private/data
                  circuit-reg-pairs)
         syntax/macro-testing)

(test-case "checking"
  (check-exn
   #rx"b: unbound identifier"
   (lambda ()
     (convert-compile-time-error
      (circuit
       #:inputs ()
       #:outputs ()
       (a = b)))))
  (check-exn
   #rx"b: unbound identifier"
   (lambda ()
     (define b #f)
     (convert-compile-time-error
      (circuit
       #:inputs ()
       #:outputs ()
       (a = b)))))
  (check-exn
   #rx"duplicate binding"
   (lambda ()
     (convert-compile-time-error
      (circuit
       #:inputs (a) #:outputs (c)
       (a = b) (b = c))))))
(test-case "variable<? is actually a total ordering"

  (check-true
   (variable<? '(+ in) '(- in)))
  (check-false
   (variable<? '(- in) '(+ in)))

  (redex-check
   classical (a b)
   (let ([a<b (variable<? (term a) (term b))]
         [b<a (variable<? (term b) (term a))])
   (if (equal? (term a) (term b))
       (equal? a<b b<a)
       (equal? a<b (not b<a))))))
(test-case "contracts"
  (check-pred
   constructive-circuit?
   (circuit
    #:inputs (c) #:outputs (a)
    (a = b) (b = c)))
  (check-pred
   constructive-circuit?
   (circuit
    #:inputs (c) #:outputs (a)
    (a = c)))
  (check-pred
   classical-circuit?
   (constructive->classical
    (circuit
     #:inputs (c) #:outputs (a)
     (a = c)))))

(test-case "verification"   
  (check-pred
   list?
   (verify-same
    (circuit
     #:inputs ()
     #:outputs () 
     (a = (and a a)))
    (circuit
     #:inputs (a)
     #:outputs (b) 
     (b = (and a a)))))
  (check-pred
   list?
   (verify-same
    (circuit
     #:inputs (x)
     #:outputs (z)
     (z = (and x a))
     (a = (or x a)))
    (circuit
     #:inputs (x)
     #:outputs (z)
     (z = x))))
  (check-pred
   list?
   (verify-same
    (circuit
     #:inputs (b) #:outputs (a)
     (a = b))
    (circuit
     #:inputs (b) #:outputs (a)
     (a = true))))
  (check-pred
   list?
   (verify-same
    (circuit
     #:inputs (I1 I2 I3)
     #:outputs (O1 O2 O3)
     (O1 = I1)
     (O2 = I2)
     (O3 = I3))
    (circuit
     #:inputs (I1 I2 I3)
     #:outputs (O3)
     (O3 = I3)))))

(test-case "verification works when an internal wire name matches an interface name"
  (check-pred
   unsat?
   (verify-same
    (circuit
     #:inputs () #:outputs (a)
     (a = false))
    (circuit
     #:inputs () #:outputs ()
     (a = true))))
  (check-pred
   unsat?
   (verify-same
    (circuit
     #:inputs (i) #:outputs (o)
     (o = (and false i)))
    (circuit
     #:inputs () #:outputs (o)
     (i = false)
     (o = i)))))
            
(test-case "construction"
  (check-equal?
   (circuit-reg-pairs
    (circuit
     #:inputs (b) #:outputs (a out)
     (a = b)
     (reg in out = a)))
   '((in out))))
(test-case "execute"
  (check-equal?
   (execute
    (circuit
     #:inputs (a)
     #:outputs (b) 
     (b = (and a a)))
    '((a true)))
   '(((a #t) (b #t))))
  (check-equal?
   (execute
    (circuit
     #:inputs (a)
     #:outputs (b) 
     (b = (and a a)))
    '((a #f)))
   '(((a #f) (b #f))))
  (check-equal?
   (execute
    (circuit
     #:inputs (b) #:outputs (a)
     (a = b))
    '((b true)))
   (list (list '(b #t) '(a #t))))
  (check-equal?
   (execute
    (circuit
     #:inputs (b) #:outputs (a out)
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
    (circuit
     #:inputs (x)
     #:outputs (z)
     (z = (and x a))
     (a = (or x a)))))
  (check-pred
   list?
   (verify-same
    (constructive->classical
     (circuit
      #:inputs (x)
      #:outputs (z)
      (z = (and x a))
      (a = (or x a))))
    (constructive->classical
     (circuit
      #:inputs (x)
      #:outputs (z)
      (z = x)))))
  (check-pred
   classical-circuit?
   (constructive->classical
    (circuit
     #:inputs (c) #:outputs (a)
     (a = c))))
  (check-equal?
   (execute
    (constructive->classical
     (circuit
      #:inputs (c) #:outputs (a)
      (a = c)))
    '(((+ c) true) ((- c) false)))
   (list (list '((+ c) #t) '((- c) #f)
               '((+ a) #t) '((- a) #f))))
  
  (check-equal?
   (execute
    (constructive->classical
     (circuit
      #:inputs (b) #:outputs (a out)
      (a = b)
      (reg in out = a)))
    '(((+ b) #t) ((- b) #f))
    '(((+ b) #f) ((- b) #t))
    '(((+ b) #f) ((- b) #t)))
   (list (list  '((+ b) #t) '((- b) #f)
               '((+ a) #t) '((- a) #f)
               '((+ in) #t) '((- in) #f)
               '((+ out) #f) '((- out) #t))
         (list '((+ b) #f) '((- b) #t)
               '((+ a) #f) '((- a) #t)
               '((+ in) #f) '((- in) #t)
               '((+ out) #t) '((- out) #f))
         (list '((+ b) #f) '((- b) #t)
               '((+ a) #f) '((- a) #t)
               '((+ in) #f) '((- in) #t)
               '((+ out) #f) '((- out) #t)))))
