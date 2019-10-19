#lang rosette/safe
(require
  "sem-sig.rkt"
  "interp-sig.rkt"
  "interp-unit.rkt"
  "three-valued-unit.rkt"
  "pos-neg-unit.rkt"
  "shared.rkt"
  (only-in "../main.rkt" convert-P convert-p)
  racket/unit
  rackunit
  rackunit/text-ui
  racket/match
  (only-in redex/reduction-semantics
           term)
  (for-syntax syntax/parse
              racket/base
              syntax/strip-context))
(define-signature test-suite^
  (suite))
(define-signature convert^
  (convert type-name convert-term convert-names defined
           convert-register-pairs))
(define-unit nothing@
  (import)
  (export convert^)
  (define type-name "B⊥")
  (define (convert x) x)
  (define (convert-names x) x)
  (define (convert-term x) x)
  (define (convert-register-pairs x) x)
  (define (defined x)
    (lambda (i)
      (not (equal? (deref i x) '⊥)))))
(define-unit tv@
  (import)
  (export convert^)
  (define type-name "TVF")
  (define (convert x)
    (term (convert-P ,x)))
  (define (convert-names x)
    (append-map (lambda (x) (list `(+ ,x) `(- ,x)))
                x))
  (define (convert-register-pairs x)
    (append-map
     (lambda (x)
       (list `((+ ,(first x)) (+ ,(second x)))
             `((- ,(first x)) (- ,(second x)))))
     x))
  (define (defined x)
    (lambda (i)
      (or (deref i `(+ ,x))
          (deref i `(- ,x)))))
  (define (convert-term x)
    ;; we only need `+, as `+ being true demands `- be false
    (term (convert-p + ,x))))


  
(define-syntax define-circuit-test-suite
  (syntax-parser
    [(_ name:id body ...)
     #`(begin
         (define-unit suite@
           (import #,(replace-context this-syntax #'sem^)
                   #,(replace-context this-syntax #'interp^)
                   #,(replace-context this-syntax #'convert^))
           (export test-suite^)
           (define (#,(replace-context this-syntax #'convert*) x)
             (map (lambda (x) (list (first x) (third x)))
                  (#,(replace-context this-syntax #'convert) x)))
           (define (#,(replace-context this-syntax #'build-state*) x)
             (map
              (lambda (x)
                (match x
                  [(list n 'true) (list n #t)]
                  [(list n 'false) (list n #f)]
                  [(list n '⊥) (list n '⊥)]))
              x))
           (define (suite)
             (test-suite #,(replace-context this-syntax #'type-name)
               body ...)))
         (define name
           (let ()
             (define-values/invoke-unit/infer
               (export (prefix three: test-suite^))
               (link interp@ three-valued@ suite@ nothing@))
             (define-values/invoke-unit/infer
               (export (prefix pm: test-suite^))
               (link interp@ pos-neg@ suite@ tv@))
             (make-test-suite
              #,(~a (symbol->string (syntax->datum #'name)))
              (list
               (three:suite)
               (pm:suite)))))
         (provide name)
         (module+ test
           (void (run-tests name))))]))

(define-circuit-test-suite basics 
  (check-true
   (outputs=?
    (eval (convert* `((a = ⊥))) (build-formula (convert `((a = (or true true))))))
    (eval (convert* `((a = ⊥))) (build-formula (convert `((a = (or true true))))))))
  (check-false
   (outputs=?
    (eval (build-state (convert`((O = (not L)) (L = I)))
                       (convert* `((I = false))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I))) (convert* `((I = false))))
          (build-formula (convert `((O = I)))))))
  (check-false
   (result=?
    (eval (build-state (convert `((O = (not L)) (L = I)))
                       (convert* `((I = false))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I))) (convert* `((I = false))))
          (build-formula (convert `((O = I)))))))
  (check-false
   (result=?
    (eval (build-state (convert`((O = (not L)) (L = I))) (convert* `((I = true))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I))) (convert* `((I = true))))
          (build-formula (convert `((O = I)))))))
  (check-true
   (result=?
    (eval (build-state (convert `((O = (not L)) (L = I))) (convert* `((I = ⊥))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I))) (convert* `((I = ⊥))))
          (build-formula (convert `((O = I)))))))
  (check-true
   (outputs=?
    (eval (convert* `((a = ⊥)))
          (build-formula (convert `((a = (or true true))))))
    (eval (convert* `((a = ⊥)))
          (build-formula (convert `((a = (or true true))))))))
  
  (check-false
   (outputs=?
    (eval (build-state (convert `((O = (not L)) (L = I)))
                       (convert* `((I = true))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I)))
                       (convert* `((I = true))))        
          (build-formula (convert `((O = I)))))))
  (check-false
   (result=?
    (eval (build-state (convert `((O = (not L)) (L = I)))
                       (convert* `((I = false))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert`((O = I)))
                       (convert* `((I = false))))
          (build-formula (convert `((O = I)))))))
  
  (check-true
   (result=?
    (eval (build-state (convert `((O = (not L)) (L = I)))
                       (convert* `((I = ⊥))))
          (build-formula (convert `((O = (not L)) (L = I)))))
    (eval (build-state (convert `((O = I)))
                       (convert* `((I = ⊥))))
          (build-formula (convert `((O = I))))))))

(define-circuit-test-suite constraints
  (check-pred
   unsat?
   (verify-same
    #:constraints (convert-term `(not (or I (not I))))
    (convert `((O = (not L)) (L = I)))
    (convert` ((O = I))))))

(define-circuit-test-suite verification
  (with-asserts-only
   (let ()
     (define symbolic (symbolic-inputs (convert `((O = L) (L = I)))))
     (define s (build-state (convert `((O = L) (L = I))) symbolic))
     (define f (build-formula (convert `((O = L) (L = I)))))
     (check-pred
      unsat?
      (verify
       (assert
        (equal?
         (deref
          (eval s f)
          (convert-term 'O))
         (deref s (convert-term 'I))))))
     (define I¬=⊥ (defined 'I))
     (check-pred
      unsat?
      (verify
       #:assume (assert (not (I¬=⊥ s)))
       #:guarantee
       (assert (not (constructive? (eval s f))))))))
  (with-asserts-only
   (let ()
     (define s (build-state (convert `((O = I)))
                            (symbolic-inputs (convert `((O = I))))))
     (define f (build-formula (convert `((O = I)))))
     (check-pred
      unsat?
      (verify
       (assert
        (equal?
         (deref
          (eval s f)
          (convert-term 'O))
         (deref s (convert-term 'I))))))
     (define I¬=⊥ (defined 'I))
     (check-pred
      unsat?
      (verify
       #:assume (assert (not (I¬=⊥ s)))
       #:guarantee
       (assert (not (constructive? (eval s f))))))))
    
  (check-pred
   unsat?
   (verify-same
    (convert `((O = L) (L = I)))
    (convert `((O = I)))))

  (check-pred
   list?
   (verify-same
    (convert `((O = (not L)) (L = I)))
    (convert `((O = I)))))
    
  (test-case "pinning tests"
    (define p1
      (convert
       '(
         ;; these come from then nothing
         (l0 = GO)
         (lsel = false)
         ;; SEL
         (SEL = (or lsel rsel))
         ;; the synchonizer
         (K0 = (and left0 (and right0 both0)))
         (left0 = (or l0 lem))
         (right0 = (or r0 rem))
         (lem = (and SEL (and RES (not lsel))))
         (rem = (and SEL (and RES (not rsel))))
         (both0 = (or l0 r0)))))
    (define p2 (convert '((K0 = r0) (SEL = rsel))))
    (check-pred
     list?
     (verify-same p1 p2))))

(define-circuit-test-suite verify/multi-is-verify
  (check-pred
   unsat?
   (verify-same
    #:register-pairs1 (list)
    #:register-pairs2 (list)
    (convert `((O = L) (L = I)))
    (convert `((O = I)))))

  (check-pred
   list?
   (verify-same
    #:register-pairs1 (list)
    #:register-pairs2 (list)
    (convert `((O = (not L)) (L = I)))
    (convert `((O = I)))))
    
  (test-case "pinning tests"
    (define p1
      (convert
       '(
         ;; these come from then nothing
         (l0 = GO)
         (lsel = false)
         ;; SEL
         (SEL = (or lsel rsel))
         ;; the synchonizer
         (K0 = (and left0 (and right0 both0)))
         (left0 = (or l0 lem))
         (right0 = (or r0 rem))
         (lem = (and SEL (and RES (not lsel))))
         (rem = (and SEL (and RES (not rsel))))
         (both0 = (or l0 r0)))))
    (define p2 (convert '((K0 = r0) (SEL = rsel))))
    (check-pred
     list?
     (verify-same
      #:register-pairs1 (list)
      #:register-pairs2 (list)
      p1 p2))))
  
(define-circuit-test-suite eval/multi
  (test-case "non states tf using equality"
    (check-equal?
     (eval/multi (list (build-state* (convert* `((a = true) (o = ⊥))))
                       (build-state* (convert* `((a = false) (o = ⊥)))))
                 (build-formula (convert `((o = a))))
                 `()
                 `())
     (list (build-state* (convert* `((a = true) (o = true))))
           (build-state* (convert* `((a = false) (o = false)))))))
  (test-case "non states tf using result=?"
    (check-true
     (result=?/multi
      (eval/multi (list (build-state* (convert* `((a = true) (o = ⊥))))
                        (build-state* (convert*  `((a = false) (o = ⊥)))))
                  (build-formula (convert `((o = a))))
                  `()
                  `())
      (list (build-state* (convert* `((a = true) (o = true))))
            (build-state* (convert* `((a = false) (o = false))))))))
  (test-case "non states tfb using result=?"
    (check-true
     (result=?/multi
      (eval/multi (list (build-state* (convert* `((a = true) (o = ⊥))))
                        (build-state* (convert* `((a = false) (o = ⊥))))
                        (build-state* (convert* `((a = ⊥) (o = ⊥))))
                        (build-state* (convert* `((a = ⊥) (o = ⊥)))))
                  (build-formula (convert `((o = a))))
                  `()
                  `())
      (list (build-state* (convert* `((a = true) (o = true))))
            (build-state* (convert* `((a = false) (o = false))))
            (build-state* (convert* `((a = ⊥) (o = ⊥))))))))
  (test-case "one state tfb using result=?"
    (check-true
     (result=?/multi
      (eval/multi (list (build-state* (convert* `((a = true) (o = ⊥) (pre-in = ⊥))))
                        (build-state* (convert* `((a = false) (o = ⊥) (pre-in = ⊥))))
                        (build-state* (convert* `((a = ⊥) (o = ⊥) (pre-in = ⊥)))))
                  (build-formula (convert `((o = a) (pre-in = o))))
                  (convert-names `(pre-in))
                  (build-state* (convert* `((pre-out = false)))))
      (list (build-state* (convert* `((pre-out = false) (a = true) (o = true) (pre-in = true))))
            (build-state* (convert* `((pre-out = true) (a = false) (o = false) (pre-in = false))))
            (build-state* (convert* `((pre-out = false) (a = ⊥) (o = ⊥) (pre-in = ⊥)))))))))
    
  
(define-circuit-test-suite verify/multi
  (check-pred
   unsat?
   (verify-same
    #:register-pairs1 (convert-register-pairs `((pre-in pre-out)))
    #:register-pairs2 (convert-register-pairs `((pre-in pre-out)))
    (convert `((o = a) (pre-in = o)))
    (convert `((o = a) (pre-in = o)))))
  (check-pred
   unsat?
   (verify-same
    #:register-pairs1 (convert-register-pairs `((pre-in1 pre-out1)
                                                (pre-in2 pre-out2)))
    #:register-pairs2 (convert-register-pairs `((pre-in pre-out)))
    #:outputs (convert-names `(O1 O2))
    (convert `((pre-in1 = I)
               (pre-in2 = I)
               (O1 = pre-out1)
               (O2 = pre-out2)))
    (convert `((pre-in = I)
               (O1 = pre-out)
               (O2 = pre-out)))))
  (check-pred
   list?
   (verify-same
    #:register-pairs1 (convert-register-pairs `((pre-in1 pre-out1)
                                                (pre-in2 pre-out2)))
    #:register-pairs2 (convert-register-pairs `((pre-in pre-out)))
    #:outputs (convert-names `(O))
    (convert `((pre-in1 = I)
               (pre-in2 = pre-out1)
               (O = pre-out2)))
    (convert `((pre-in = I) (O = pre-out))))))

(define-circuit-test-suite regression-tests
  (test-case "case found when debugging abort"
    (define q
      (convert `((SEL = q_SEL)
                 (K0 = q_K0)
                 (Kn = q_Kn))))
    (define start
      (convert
       `(;; p
         (p_GO = (and GO S))
         (p_RES = RES)
         ;; these wires are not needed for the proof, and are never read so we can 
         ;; ignore them
         ;(p_SUSP = SUSP)
         ;(p_KILL = KILL)
         ;; q
         (q_GO = (and GO (not S)))
         (q_RES = RES)
         ;; these wires are not needed for the proof, and are never read so we can 
         ;; ignore them
         ;(q_SUSP = SUSP)
         ;(q_KILL = KILL)
         ;; out
         (SEL = (or p_SEL q_SEL))
         (K0 = (or p_K0 q_K0))
         (Kn = (or p_Kn q_Kn)))))
    (test-case "negative version"
      (check-pred
       list?
       (verify-same
        #:outputs (convert-names '(SEL Kn K0))
        #:constraints
        (convert-term
         '(and (implies SEL (not GO))
               (implies (not SEL) (not S))))
        start
        q)))
    (test-case "positive version"
      (check-pred
       unsat?
       (verify-same
        #:outputs (convert-names '(SEL Kn K0))
        #:constraints
        (convert-term
         '(and (implies SEL (not GO))
               (and (implies (not SEL) (not S))
                    (and (implies (not (or p_GO (and p_SEL p_RES)))
                                  (and (not p_Kn) (not p_K0)))
                         (implies (not (or p_GO (and p_SEL p_RES)))
                                  (and (not p_Kn) (not p_K0)))))))
        start
        q)))))
     
    

(module+ test

  ;                                                    
  ;                                                    
  ;                                                    
  ;              ;                                     
  ;   ;;;;;;;;;  ;                                     
  ;      ;;      ;                                     
  ;      ;;      ;                                     
  ;      ;;      ; ;;;;    ;;  ;;;    ;;;;      ;;;;   
  ;      ;;      ;;   ;     ; ;  ;   ;;  ;;    ;;  ;;  
  ;      ;;      ;    ;;    ;;   ;   ;    ;;   ;    ;; 
  ;      ;;      ;    ;;    ;;      ;;    ;;  ;;    ;; 
  ;      ;;      ;    ;;    ;;      ;;;;;;;;  ;;;;;;;; 
  ;      ;;      ;    ;;    ;;      ;;        ;;       
  ;      ;;      ;    ;;    ;;       ;         ;       
  ;      ;;      ;    ;;    ;;       ;;   ;    ;;   ;  
  ;      ;;      ;    ;;   ;;;;       ;;;;;;    ;;;;;; 
  ;                                                    
  ;                                                    
  ;                                                    
  ;                                                    
  ;                                                    

        

  (test-case "three valued"
    (define-values/invoke-unit/infer
      (export interp^ sem^)
      (link three-valued@ interp@))
    (test-case "basic verify equality"
      (define-symbolic I1* boolean?)
      (define-symbolic I2* boolean?)
      (define I (if I1* '⊥ I2*))
      (check-true
       (unsat?
        (verify
         (assert
          (result=? (eval `((O ,'⊥) (L ,'⊥) (I ,I))
                          `((O ,(lambda (x) (deref x 'L)))
                            (L ,(lambda (x) (deref x 'I)))))
                    (eval `((O ,'⊥) (I ,I))
                          `((O ,(lambda (x) (deref x 'I)))))))))))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
           `((O ,(lambda (x) (deref x 'L)))
             (L ,(lambda (x) (deref x 'I)))))
     `((O ,#t) (L ,#t) (I ,#t)))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
           `((O ,(lambda (x) (deref x 'L)))
             (L ,(lambda (x) (deref x 'I)))))
     `((O ,#f) (L ,#f) (I ,#f)))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
           `((O ,(lambda (x) (deref x 'L)))
             (L ,(lambda (x) (deref x 'I)))))
     `((O ,'⊥) (L ,'⊥) (I ,'⊥)))
  
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
            `((O ,(lambda (x) (deref x 'L)))
              (L ,(lambda (x) (deref x 'I)))))
      `((O ,#t) (L ,#t) (I ,#t))))
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
            `((O ,(lambda (x) (deref x 'L)))
              (L ,(lambda (x) (deref x 'I)))))
      `((O ,#f) (L ,#f) (I ,#f))))
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
            `((O ,(lambda (x) (deref x 'L)))
              (L ,(lambda (x) (deref x 'I)))))
      `((O ,'⊥) (L ,'⊥) (I ,'⊥))))
    (test-case "formula building"
      (define f (build-formula `((O = L) (L = I))))
      (check-equal?
       (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
             f)
       `((O ,#t) (L ,#t) (I ,#t)))
      (check-equal?
       (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
             f)
       `((O ,#f) (L ,#f) (I ,#f)))
      (check-equal?
       (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
             f)
       `((O ,'⊥) (L ,'⊥) (I ,'⊥)))
      (check-true
       (result=?
        (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
              f)
        `((O ,#t) (L ,#t) (I ,#t))))
      (check-true
       (result=?
        (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
              f)
        `((O ,#f) (L ,#f) (I ,#f))))
      (check-true
       (result=?
        (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
              f)
        `((O ,'⊥) (L ,'⊥) (I ,'⊥))))))
      


  ;                                                                               
  ;                                                                               
  ;                                                                               
  ;                                                                               
  ;    ;;;;;;                                     ;;;    ;                        
  ;    ;;   ;;                                    ;;;    ;                        
  ;    ;;    ;;                                   ;;;;   ;                      ; 
  ;    ;;    ;;    ;;;;       ;;;;;               ;;;;   ;      ;;;;      ;;;;;;; 
  ;    ;;    ;;   ;;   ;;    ;;   ;;              ;; ;   ;    ;;   ;;    ;;  ;;   
  ;    ;;    ;;   ;    ;;    ;                    ;; ;;  ;    ;     ;    ;    ;;  
  ;    ;;   ;;   ;;     ;    ;;                   ;; ;;  ;    ;     ;   ;;    ;;  
  ;    ;;;;;;    ;;     ;     ;;;;      ;;;;;;;   ;;  ;; ;   ;;;;;;;;    ;    ;;  
  ;    ;;        ;;     ;       ;;;               ;;  ;; ;   ;;          ;;   ;   
  ;    ;;        ;;     ;         ;;              ;;   ; ;    ;           ;;;;;   
  ;    ;;         ;    ;;         ;;              ;;   ;;;    ;;         ;        
  ;    ;;         ;;  ;;;    ;;  ;;;              ;;    ;;    ;;;  ;;    ;;       
  ;    ;;          ;;;;     ; ;;;;                ;;    ;;      ;;;;      ;;;;;;  
  ;                                                                            ;; 
  ;                                                                     ;;     ;; 
  ;                                                                     ;;    ;;  
  ;                                                                      ;;;;;;   
  ;                                                                               


  (test-case "Pos Neg"
    (define-values/invoke-unit/infer
      (export interp^ sem^)
      (link pos-neg@ interp@))
    (test-case "basic verify equality"
      (define-symbolic \+I boolean?)
      (define-symbolic \-I boolean?)
    
      (check-true
       (unsat?
        (verify
         (assert
          (result=? (eval `(((+ O) ,#f)
                            ((- O) ,#f)
                            ((+ L) ,#f)
                            ((- L) ,#f)
                            ((+ I) ,\+I)
                            ((- I) ,\-I))
                          `(((+ O) ,(lambda (x) (deref x '(+ L))))
                            ((- O) ,(lambda (x) (deref x '(- L))))
                            ((+ L) ,(lambda (x) (deref x '(+ I))))
                            ((- L) ,(lambda (x) (deref x '(- I))))))
                    (eval `(((+ O) ,#f)
                            ((- O) ,#f)
                            ((+ I) ,\+I)
                            ((- I) ,\-I))
                          `(((+ O) ,(lambda (x) (deref x '(+ I))))
                            ((- O) ,(lambda (x) (deref x '(- I))))))))))))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#t)
             ((- I) ,#f))
           `(((+ O) ,(lambda (x) (deref x '(+ L))))
             ((- O) ,(lambda (x) (deref x '(- L))))
             ((+ L) ,(lambda (x) (deref x '(+ I))))
             ((- L) ,(lambda (x) (deref x '(- I))))))
     `(((+ O) ,#t)
       ((- O) ,#f)
       ((+ L) ,#t)
       ((- L) ,#f)
       ((+ I) ,#t)
       ((- I) ,#f)))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#f)
             ((- I) ,#t))
           `(((+ O) ,(lambda (x) (deref x '(+ L))))
             ((- O) ,(lambda (x) (deref x '(- L))))
             ((+ L) ,(lambda (x) (deref x '(+ I))))
             ((- L) ,(lambda (x) (deref x '(- I))))))
     `(((+ O) ,#f)
       ((- O) ,#t)
       ((+ L) ,#f)
       ((- L) ,#t)
       ((+ I) ,#f)
       ((- I) ,#t)))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#f)
             ((- I) ,#f))
           `(((+ O) ,(lambda (x) (deref x '(+ L))))
             ((- O) ,(lambda (x) (deref x '(- L))))
             ((+ L) ,(lambda (x) (deref x '(+ I))))
             ((- L) ,(lambda (x) (deref x '(- I))))))
     `(((+ O) ,#f)
       ((- O) ,#f)
       ((+ L) ,#f)
       ((- L) ,#f)
       ((+ I) ,#f)
       ((- I) ,#f)))
  
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#t)
              ((- I) ,#f))
            `(((+ O) ,(lambda (x) (deref x '(+ L))))
              ((- O) ,(lambda (x) (deref x '(- L))))
              ((+ L) ,(lambda (x) (deref x '(+ I))))
              ((- L) ,(lambda (x) (deref x '(- I))))))
      `(((+ O) ,#t)
        ((- O) ,#f)
        ((+ L) ,#t)
        ((- L) ,#f)
        ((+ I) ,#t)
        ((- I) ,#f))))
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#f)
              ((- I) ,#t))
            `(((+ O) ,(lambda (x) (deref x '(+ L))))
              ((- O) ,(lambda (x) (deref x '(- L))))
              ((+ L) ,(lambda (x) (deref x '(+ I))))
              ((- L) ,(lambda (x) (deref x '(- I))))))
      `(((+ O) ,#f)
        ((- O) ,#t)
        ((+ L) ,#f)
        ((- L) ,#t)
        ((+ I) ,#f)
        ((- I) ,#t))))
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#f)
              ((- I) ,#f))
            `(((+ O) ,(lambda (x) (deref x '(+ L))))
              ((- O) ,(lambda (x) (deref x '(- L))))
              ((+ L) ,(lambda (x) (deref x '(+ I))))
              ((- L) ,(lambda (x) (deref x '(- I))))))
      `(((+ O) ,#f)
        ((- O) ,#f)
        ((+ L) ,#f)
        ((- L) ,#f)
        ((+ I) ,#f)
        ((- I) ,#f))))
    (test-case "formula building"
      (define f (build-formula (term (convert-P ((O = L) (L = I))))))
      (check-equal?
       (eval `(((+ O) ,#f)
               ((- O) ,#f)
               ((+ L) ,#f)
               ((- L) ,#f)
               ((+ I) ,#t)
               ((- I) ,#f))
             f)
       `(((+ O) ,#t)
         ((- O) ,#f)
         ((+ L) ,#t)
         ((- L) ,#f)
         ((+ I) ,#t)
         ((- I) ,#f)))
      (check-equal?
       (eval `(((+ O) ,#f)
               ((- O) ,#f)
               ((+ L) ,#f)
               ((- L) ,#f)
               ((+ I) ,#f)
               ((- I) ,#t))
             f)
       `(((+ O) ,#f)
         ((- O) ,#t)
         ((+ L) ,#f)
         ((- L) ,#t)
         ((+ I) ,#f)
         ((- I) ,#t)))
      (check-equal?
       (eval `(((+ O) ,#f)
               ((- O) ,#f)
               ((+ L) ,#f)
               ((- L) ,#f)
               ((+ I) ,#f)
               ((- I) ,#f))
             f)
       `(((+ O) ,#f)
         ((- O) ,#f)
         ((+ L) ,#f)
         ((- L) ,#f)
         ((+ I) ,#f)
         ((- I) ,#f)))
      (check-true
       (result=?
        (eval `(((+ O) ,#f)
                ((- O) ,#f)
                ((+ L) ,#f)
                ((- L) ,#f)
                ((+ I) ,#t)
                ((- I) ,#f))
              f)
        `(((+ O) ,#t)
          ((- O) ,#f)
          ((+ L) ,#t)
          ((- L) ,#f)
          ((+ I) ,#t)
          ((- I) ,#f))))
      (check-true
       (result=?
        (eval `(((+ O) ,#f)
                ((- O) ,#f)
                ((+ L) ,#f)
                ((- L) ,#f)
                ((+ I) ,#f)
                ((- I) ,#t))
              f)
        `(((+ O) ,#f)
          ((- O) ,#t)
          ((+ L) ,#f)
          ((- L) ,#t)
          ((+ I) ,#f)
          ((- I) ,#t))))
      (check-true
       (result=?
        (eval `(((+ O) ,#f)
                ((- O) ,#f)
                ((+ L) ,#f)
                ((- L) ,#f)
                ((+ I) ,#f)
                ((- I) ,#f))
              f)
        `(((+ O) ,#f)
          ((- O) ,#f)
          ((+ L) ,#f)
          ((- L) ,#f)
          ((+ I) ,#f)
          ((- I) ,#f)))))))