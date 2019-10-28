#lang racket
(require rackunit
         circuitous
         (except-in circuitous/private/redex FV)
         redex/reduction-semantics
         (only-in circuitous/private/data
                  circuit-reg-pairs)
         (for-syntax syntax/parse)
         syntax/macro-testing
         racket/logging
         (only-in rosette/solver/solution
                  model
                  core))

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
     (a = c))))

  (check-exn
   #rx"contract violation.*#:pre condition violation"
   (lambda ()
     (assert-same
      #:constraints 'Unbound
      (circuit
       #:inputs () #:outputs ())
      (circuit
       #:inputs () #:outputs ())))))

(test-case "constructive"
  (check-pred
   list?
   (verify-totally-constructive
    (circuit
     #:inputs ()
     #:outputs ()
     (a = a))))
  (check-pred
   list?
   (verify-totally-constructive
    (constructive->classical
     (circuit
      #:inputs ()
      #:outputs ()
      (a = a)))))
  (check-pred
   list?
   (verify-totally-constructive
    (circuit
     #:inputs (A)
     #:outputs ()
     (O = (or A O)))))
  (check-pred
   unsat?
   (verify-totally-constructive
    (circuit
     #:inputs (A)
     #:outputs ()
     (O = (or A (or (not A) O))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    (circuit
     #:inputs ()
     #:outputs ())))
  (check-pred
   unsat?
   (verify-totally-constructive
    (constructive->classical
     (circuit
      #:inputs ()
      #:outputs ()))))
  (check-pred
   unsat?
   (verify-totally-constructive
    (circuit
     #:inputs (I)
     #:outputs ()
     (O = (and I (not I))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    (constructive->classical
     (circuit
      #:inputs (I)
      #:outputs ()
      (O = (and I (not I)))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    #:constraints '(or I (not I))
    (circuit
     #:inputs (I)
     #:outputs ()
     (O = (and I (not I))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    #:constraints '(or (+ I) (- I))
    (constructive->classical 
     (circuit
      #:inputs (I)
      #:outputs ()
      (O = (and I (not I)))))))

  
  (check-pred
   unsat?
   (verify-totally-constructive
    (circuit
     #:inputs (I)
     #:outputs (O)
     (O = (and I (not I))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    (constructive->classical
     (circuit
      #:inputs (I)
      #:outputs (O)
      (O = (and I (not I)))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    #:constraints '(or I (not I))
    (circuit
     #:inputs (I)
     #:outputs (O)
     (O = (and I (not I))))))
  (check-pred
   unsat?
   (verify-totally-constructive
    #:constraints '(or (+ I) (- I))
    (constructive->classical 
     (circuit
      #:inputs (I)
      #:outputs (O)
      (O = (and I (not I))))))))

(test-case "verification symmetry under constraints"
  (define-check (check-sym a b c)
    (define p (verify-same #:constraints a b c))
    (define q (verify-same #:constraints a c b))
    (unless
        (or (and (unsat? p) (unsat? q))
            (and (list? p) (list? q)))
      (fail-check)))
  (check-sym
   `O
   (circuit
    #:inputs (I)
    #:outputs (O)
    (O = I))
   (circuit
    #:inputs (I)
    #:outputs (O)
    (X = I)
    (O = true))))

(test-case "verification"
  (check-pred
   list?
   (verify-same
    (circuit
     #:inputs (I)
     #:outputs ()
     (O = (and I (not I))))
    (circuit
     #:inputs ()
     #:outputs ())))
  (check-pred
   list?
   (verify-same
    (constructive->classical 
     (circuit
      #:inputs (I)
      #:outputs ()
      (O = (and I (not I)))))
    (constructive->classical
     (circuit
      #:inputs ()
      #:outputs ()))))
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
   list?
   (verify-same
    (circuit
     #:inputs (i) #:outputs (o)
     (o = (and false i)))
    (circuit
     #:inputs () #:outputs (o)
     (i = false)
     (o = i))))
  (check-pred
   list?
   (verify-same
    (constructive->classical
     (circuit
      #:inputs (i) #:outputs (o)
      (o = (and false i))))
    (constructive->classical
     (circuit
      #:inputs () #:outputs (o)
      (i = false)
      (o = i)))))
  (check-pred
   unsat?
   (verify-same
    #:constraints `(or i (not i))
    (circuit
     #:inputs (i) #:outputs (o)
     (o = (and false i)))
    (circuit
     #:inputs () #:outputs (o)
     (i = false)
     (o = i))))
  (check-pred
   unsat?
   (verify-same
    #:constraints `(or (+ i) (- i))
    (constructive->classical
     (circuit
      #:inputs (i) #:outputs (o)
      (o = (and false i))))
    (constructive->classical
     (circuit
      #:inputs () #:outputs (o)
      (i = false)
      (o = i))))))
            
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

(test-case "register tracking"
  (define c1
    (circuit
     #:inputs (a)
     #:outputs (out)
     (reg in out = a)))
  (define c2
    (circuit
     #:inputs (a)
     #:outputs (out)
     (reg in out = (not a))))

  (define c3
    (circuit
     #:inputs ()
     #:outputs (out)
     (out = false)))
  (define x (verify-same c2 c3))
  (check-pred list? x)
  (check-equal?
   (length (hash-keys (model (first x))))
   4
   (pretty-format (hash-keys (model (first x)))))
  
  (check-pred
   list?
   (verify-same c1 c2))
  (check-pred
   list?
   (verify-same
    (constructive->classical c1)
    (constructive->classical c2)))
  (check-pred
   list?
   (verify-same
    (constructive->classical c2)
    (constructive->classical c3))))
(test-case "dont generate symbolics for internal register names"
  (define c1
    (circuit
     #:inputs (a)
     #:outputs (out)
     (out = q)
     (reg in q = a)))
  (define c2
    (circuit
     #:inputs (a)
     #:outputs (out)
     (out = q)
     (reg in q = (not a))))

  (define c3
    (circuit
     #:inputs ()
     #:outputs (out)
     (out = false)))
  (define x (verify-same c2 c3))
  (check-pred list? x)
  (check-equal?
   (length (hash-keys (model (first x))))
   4
   (pretty-format (hash-keys (model (first x)))))
  
  (check-pred
   list?
   (verify-same c1 c2))
  (check-pred
   list?
   (verify-same
    (constructive->classical c1)
    (constructive->classical c2)))
  (check-pred
   list?
   (verify-same
    (constructive->classical c2)
    (constructive->classical c3))))


(test-case "regression test from esterel compiler+Can+registers"
  (define (only r . i)
    (map
     (lambda (x)
       (map (lambda (i)
              (or (assoc i x)
                  (list i #f)))
            i))
     r))
  (define p
    (circuit
     #:inputs (GO SUSP RES KILL)
     #:outputs (K0 K1 S1 SEL)
     (K0 = K0-internal)
     (K0-internal = (and reg-out RES))
     (K0-internal1 = (or then else))
     (K1 = K0-internal1)
     (S1 = then)
     (S3 = K0-internal)
     (SEL = (or (or false false) reg-out))
     (do-sel = (or K0-internal1 resel))
     (else = (and GO (not S3)))
     (reg reg-in reg-out = (and (not KILL) do-sel))
     (resel = (and SUSP SEL))
     (then = (and GO S3))))
  (define q
    (circuit
     #:inputs (GO SUSP RES KILL)
     #:outputs (K0 K1 SEL)
     (K0 = K0-internal)
     (K0-internal = (and reg-out RES))
     (K0-internal1 = GO)
     (K1 = K0-internal1)
     (S2 = K0-internal)
     (SEL = reg-out)
     (do-sel = (or K0-internal1 resel))
     (reg reg-in reg-out = (and (not KILL) do-sel))
     (resel = (and SUSP SEL))))
  (check-equal?
   (only
    (execute p
             '((GO true) (RES true) (SUSP false) (KILL false))
             '((GO true) (RES true) (SUSP false) (KILL false)))
    'S1)
   '(((S1 #f))
     ((S1 #t))))
  (check-equal?
   (only
    (execute q
             '((GO true) (RES true) (SUSP false) (KILL false))
             '((GO true) (RES true) (SUSP false) (KILL false)))
    'S1)
   '(((S1 #f))
     ((S1 #f))))
  (check-not-equal?
   (only
    (execute p
             '((GO true) (RES true) (SUSP false) (KILL false))
             '((GO true) (RES true) (SUSP false) (KILL false)))
    'K0 'K1 'S1)
   (only
    (execute q
             '((GO true) (RES true) (SUSP false) (KILL false))
             '((GO true) (RES true) (SUSP false) (KILL false)))
    'K0 'K1 'S1))
  (check-pred
   list?
   (verify-same
    p q))
  (check-pred
   unsat?
   (verify-same
    #:constraints (term (implies SEL (not GO)))
    p q))
  (check-pred
   list?
   (verify-same
    (constructive->classical p)
    (constructive->classical q)))
  (check-pred
   unsat?
   (verify-same
    #:constraints (term (implies (+ SEL) (- GO)))
    (constructive->classical p)
    (constructive->classical q))))

(test-case "regression test from debugging of abort"
  (check-pred
   list?
   (verify-same
    #:constraints
    '(and (implies SEL (not GO))
          (and (implies (not SEL) (not S))
               (and (implies (not (or (and GO S) (and p_SEL RES)))
                             (and (not p_Kn) (not p_K0)))
                    (implies (not (or (and GO (not S)) (and q_SEL RES)))
                             (and (not q_Kn) (not q_K0))))))
    (circuit
     #:inputs (GO S RES p_SEL q_SEL p_K0 q_K0 p_Kn q_Kn)
     #:outputs (SEL Kn K0)
     (p_GO = (and GO S))
     (p_RES = RES)
     (q_GO = (and GO (not S)))
     (q_RES = RES)
     (SEL = (or p_SEL q_SEL))
     (K0 = (or p_K0 q_K0))
     (Kn = (or p_Kn q_Kn)))
    (circuit
     #:inputs (q_SEL q_K0 q_Kn)
     #:outputs (SEL Kn K0)
     (SEL = q_SEL)
     (K0 = q_K0)
     (Kn = q_Kn)))))

(test-case "regression test from esterel with par and guard"
  (define-syntax test
    (syntax-parser
      [(_ p q)
       #`(begin
           #,(syntax/loc this-syntax
               (check-pred list? (verify-same p q)))
           #,(syntax/loc this-syntax
               (check-pred unsat?
                           (verify-same
                            #:constraints '(implies SEL (not GO))
                            p q))))]))
  (define p/guard-simp
    (circuit
     #:outputs (K0 K1 SEL)
     #:inputs (GO)
     (GO-safe = (and GO (not SEL)))
     (K0 = (and lem1 (and rem1 SEL)))
     (K1 = (and lem2 (and rem2 GO-safe)))
     (SEL = (or psel qsel))
     (lem = (and qsel (not psel)))
     (lem1 = (or lem psel))
     (lem2 = (or lem1 GO-safe))
     (reg do-sel psel = (or GO-safe qsel))
     (reg do-sel1 qsel = (or GO-safe psel))
     (rem = (and psel (not qsel)))
     (rem1 = (or rem qsel))
     (rem2 = (or rem1 GO-safe))))
  (define p-simp
    (circuit
     #:outputs (K0 K1 SEL)
     #:inputs (GO)
     (K0 = (and lem1 (and rem1 SEL)))
     (K1 = (and lem2 (and rem2 GO)))
     (SEL = (or psel qsel))
     (lem = (and qsel (not psel)))
     (lem1 = (or lem psel))
     (lem2 = (or lem1 GO))
     (reg do-sel psel = (or GO psel))
     (reg do-sel1 qsel = (or GO qsel))
     (rem = (and psel (not qsel)))
     (rem1 = (or rem qsel))
     (rem2 = (or rem1 GO))))
  (define p/guard
    (circuit
     #:outputs (K0 K1 SEL)
     #:inputs (GO KILL RES SUSP)
     (GO-safe = (and GO (not SEL)))
     (K0 = (and lem1 (and rem1 both)))
     (K1 = (and lem2 (and rem2 both1)))
     (SEL = (or psel qsel))
     (both = (or lname rname))
     (both1 = (or lname1 rname1))
     (do-sel = (or GO-safe resel))
     (do-sel1 = (or GO-safe resel1))
     (killout = KILL)
     (lem = (and SEL (and RES (not psel))))
     (lem1 = (or lem lname))
     (lem2 = (or lem1 lname1))
     (lname = (and reg-out RES))
     (lname1 = GO-safe)
     (psel = reg-out)
     (qsel = reg-out1)
     (reg reg-in reg-out = (and (not killout) do-sel))
     (reg reg-in1 reg-out1 = (and (not killout) do-sel1))
     (rem = (and SEL (and RES (not qsel))))
     (rem1 = (or rem rname))
     (rem2 = (or rem1 rname1))
     (resel = (and SUSP psel))
     (resel1 = (and SUSP qsel))
     (rname = (and reg-out1 RES))
     (rname1 = GO-safe)))
  (define p
    (circuit
     #:outputs (K0 K1 SEL)
     #:inputs (GO KILL RES SUSP)
     (K0 = (and lem1 (and rem1 both)))
     (K1 = (and lem2 (and rem2 both1)))
     (SEL = (or psel qsel))
     (both = (or lname rname))
     (both1 = (or lname1 rname1))
     (do-sel = (or GO resel))
     (do-sel1 = (or GO resel1))
     (killout = KILL)
     (lem = (and SEL (and RES (not psel))))
     (lem1 = (or lem lname))
     (lem2 = (or lem1 lname1))
     (lname = (and reg-out RES))
     (lname1 = GO)
     (psel = reg-out)
     (qsel = reg-out1)
     (reg reg-in reg-out = (and (not killout) do-sel))
     (reg reg-in1 reg-out1 = (and (not killout) do-sel1))
     (rem = (and SEL (and RES (not qsel))))
     (rem1 = (or rem rname))
     (rem2 = (or rem1 rname1))
     (resel = (and SUSP psel))
     (resel1 = (and SUSP qsel))
     (rname = (and reg-out1 RES))
     (rname1 = GO)))

  (check-equal?
   (map (lambda (x)
          (list (assoc 'K0 x)
                (assoc 'K1 x)))
        (execute
         p/guard-simp
         '([GO true])
         '([GO true])))
   '(((K0 #f)
      (K1 #t))
     ((K0 #t)
      (K1 #f))))
  (check-equal?
   (map (lambda (x)
          (list (assoc 'K0 x)
                (assoc 'K1 x)))
        (execute
         p-simp
         '([GO true])
         '([GO true])))
   '(((K0 #f)
      (K1 #t))
     ((K0 #t)
      (K1 #t))))
  (test p/guard-simp p-simp)
  (test p-simp p/guard-simp)
  (test p/guard p)
  (test p p/guard))
  
