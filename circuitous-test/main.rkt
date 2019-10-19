#lang racket
(require redex/reduction-semantics
         (for-syntax syntax/parse)
         racket/syntax
         racket/hash
         "rosette.rkt")
(provide
 (except-out (all-defined-out) assert-same)
 (rename-out [assert-same assert-same/redex]
             [assert-same/smt assert-same]))


(module+ test (require rackunit))

(define-logger circuits)

(define-syntax define/ppl 
 (syntax-parser
   #:literals (propigate/remove*)
   [(_ name f:id before body ...) 
    #'(begin (define-term name (f before body ...))
             (assert-same/smt (term before) (term name))
             (for-each pretty-write (term name)))]
   [(_ name #:no-check
       body) 
    #'(begin (define-term name body)
             (for-each pretty-write (term name)))]))

(define-language constructive
  (P ::= (e ...))
  (e ::= (a = p))
  (p q ::= (and p q) (or p q) (not p) const a)
  (a b c ::= (variable-except true false ⊥))
  (const ::= true false ⊥)
  (C ::=
     hole
     (and C p)
     (and p C)
     (or C p)
     (or p C)
     (not C)))

(define-language classical
  (P ::= (e ...))
  (e ::= (a = p))
  (p q ::= (and p q) (or p q) (not p) const a)
  (a b c ::= (ann a*) a*)
  (ann ::= + -)
  (a* b* ::= variable-not-otherwise-mentioned)
  (const ::= true false)
  (C ::=
     hole
     (and C p)
     (and p C)
     (or C p)
     (or p C)
     (not C)))
     

(define-union-language both (class: classical) (con: constructive))

(define-syntax assert!
  (syntax-parser
    [(_ e:expr)
     #`
     (unless e
       #,(syntax/loc this-syntax
           (error 'assert! (pretty-format 'e))))]))


(define-metafunction both
  convert-P : con:P -> class:P
  [(convert-P ()) ()]
  [(convert-P (con:e_1 con:e ...))
   (class:e_1 class:e_2 class:e_rest ...)
   (where (class:e_1 class:e_2)
          (convert-e con:e_1))
   (where (class:e_rest ...)
          (convert-P (con:e ...)))])

(define-metafunction both
  convert-e : con:e -> (class:e class:e)
  [(convert-e (con:a = con:p))
   (((+ con:a) = (convert-p + con:p))
    ((- con:a) = (convert-p - con:p)))])

(define-extended-language both+implies both
  (con:p con:q ::= .... (implies con:p con:q))
  (class:p class:q ::= .... (implies class:p class:q)))
(define-metafunction both+implies
  convert-p : class:ann con:p -> class:p
  [(convert-p + (and con:p con:q))
   (and (convert-p + con:p) (convert-p + con:q))]
  [(convert-p - (and con:p con:q))
   (or (convert-p - con:p) (convert-p - con:q))]
  [(convert-p + (or con:p con:q))
   (or (convert-p + con:p) (convert-p + con:q))]
  [(convert-p - (or con:p con:q))
   (and (convert-p - con:p) (convert-p - con:q))]
  [(convert-p - (not con:p))
   (convert-p + con:p)]
  [(convert-p + (not con:p))
   (convert-p - con:p)]
  [(convert-p class:ann con:a)
   (class:ann con:a)]
  [(convert-p + true)
   true]
  [(convert-p - true)
   false]
  [(convert-p + false)
   false]
  [(convert-p - false)
   true]
  [(convert-p + ⊥)
   false]
  [(convert-p - ⊥)
   false]
  ;; TODO this are not validated
  [(convert-p + (implies con:p con:q))
   (or (convert-p - con:p)
       (and (convert-p + con:p)
            (convert-p + con:q)))]
  [(convert-p - (implies con:p con:q))
   (and (convert-p + con:p)
        (convert-p - con:q))])

(module+ test
  (check-equal?
   (term (convert-P ((a = b))))
   (term (((+ a) = (+ b)) ((- a) = (- b))))))

#|
The COS circuit for:

|#
#;(signal S1
    (present
     S1
     (seq
      (emit S2)
      (present
       S2
       nothing
       (emit S1)))
     nothing))

(define a-circuit
  (term
   ([START = true]
    [present-S1-else = (and (not S1) START)]
    [present-S1-then = (and S1 START)]
    [S2 = present-S1-then]
    [present-S2-then = (and S2 present-S1-then)]
    [present-S2-else = (and (not S2) present-S1-then)]
    [S1 = present-S2-else]
    [present-S2-term = (or present-S2-else present-S2-else)]
    [term = (or present-S1-else
                present-S2-term)])))
(define b-circuit (term (convert-P ,a-circuit)))

(define-metafunction classical
  remove : P a ... -> P
  [(remove P) P]
  [(remove (e_1 ... (a = p) e_2 ...) a b ...)
   (remove (e_1 ... e_2 ...) b ...)])

(define-metafunction classical
  propigate/remove* : P a ... -> P
  [(propigate/remove* P a ...)
   (remove (propigate* P a ...) a ...)])

(define-metafunction classical
  propigate* : P a ... -> P
  [(propigate* P) P]
  [(propigate* P a b ...)
   (propigate* (propigate P a) b ...)])

(define-metafunction classical
  propigate : P a -> P
  [(propigate P a)
   (replace P a (get a P))])

(define-metafunction classical
  get : a P -> p
  [(get a (_ ... (a = p) _ ...))
   p])

(define-metafunction classical
  rename* : P a a -> P
  [(rename* P a_1 a_2)
   (e_1 ... (a_2 = p) e_2 ...)
   (where (e_1 ... (a_1 = p) e_2 ...)
          (replace* P (a_1 a_2)))]
  [(rename* P a_1 a_2)
   (replace* P (a_1 a_2))])

(define-metafunction classical
  replace* : P (p p) ... -> P
  [(replace* P) P]
  [(replace* P (q_1 q_2) any_r ...)
   (replace* (replace P q_1 q_2) any_r ...)])

(define-metafunction classical
  replace : P p p -> P
  [(replace ((a = p) ...) q_1 q_2)
   ((a = (replace-p p q_1 q_2)) ...)])
(define-metafunction classical
  replace-p : p p p -> p
  [(replace-p q_1 q_1 q_2)
   q_2]
  [(replace-p (not p)  q_1 q_2)
   (not (replace-p p q_1 q_2))]
  [(replace-p (and p q)  q_1 q_2)
   (and (replace-p p q_1 q_2)
        (replace-p q q_1 q_2))]
  [(replace-p (or p q)  q_1 q_2)
   (or (replace-p p q_1 q_2)
       (replace-p q q_1 q_2))]
  [(replace-p p_other  q_1 q_2)
   p_other])

;                                              
;                                              
;                                              
;                                    ;;;;;     
;    ;;;;;;;                            ;;     
;    ;;                                 ;;     
;    ;;                                 ;;     
;    ;;        ;;     ;;   ;;;;;        ;;     
;    ;;         ;     ;    ;   ;;       ;;     
;    ;;         ;;   ;;         ;;      ;;     
;    ;;;;;;     ;;   ;;         ;;      ;;     
;    ;;          ;   ;      ;;;;;;      ;;     
;    ;;          ;  ;;     ;;   ;;      ;;     
;    ;;          ;; ;     ;;    ;;      ;;     
;    ;;           ; ;     ;;    ;;      ;;     
;    ;;           ;;;      ;;  ;;;      ;;  ;  
;    ;;;;;;;      ;;       ;;;;  ;       ;;;;  
;                                              
;                                              
;                                              
;                                              
;                                              

(define-metafunction constructive
  ;; first output P is the input
  ;; second is the result of evaling P_a with the first
  ;; this is the result of evaling P_b with the first
  interp-both-con : P P -> ((P P P) ...)
  [(interp-both-con P_a P_b)
   ((P_I P_1 P_2) ...)
   (where (((a = const) ...) ...)
          (all-con P_a))
   (where ((P_I (P_1) (P_2)) ...)
          ((((a = const) ...)
            (eval-con P_a ((a = const) ...))
            (eval-con P_b ((a = const) ...)))
           ...))])
(define-metafunction classical
  ;; ditto
  interp-both-class : P P -> ((P P P) ...)
  [(interp-both-class P_a P_b)
   ((P_I P_1 P_2) ...)
   (where (((a = const) ...) ...)
          (all-class P_a))
   (where ((P_I (P_1) (P_2)) ...)
          ((((a = const) ...)
            (eval-clas P_a ((a = const) ...))
            (eval-clas P_b ((a = const) ...)))
           ...))])

(define-metafunction constructive
  interp-con : P -> (P ...)
  [(interp-con P)
   (P_1 ... ...)
   (where (((a = const) ...) ...)
          (all-con P))
   (where ((P_1 ...) ...)
          ((eval-con P ((a = const) ...)) ...))])
(define-metafunction classical
  interp-class : P -> (P ...)
  [(interp-class P)
   (P_1 ... ...)
   (where (((a = const) ...) ...)
          (all-class P))
   (where ((P_1 ...) ...)
          ((eval-clas P ((a = const) ...)) ...))])
   
(define-metafunction constructive
  all-con : P -> (((a = const) ...) ...)
  [(all-con ((a = p) ...))
   (get-vals-con
   ,(remove-duplicates
     (remove* (term (a ...))
              (term (b ... ...)))))
   (where ((b ...) ...)
          ((vars p) ...))])

(define-metafunction constructive
  get-vals-con : (a ...) -> (((a = const) ...) ...)
  [(get-vals-con ()) (())]
  [(get-vals-con (a b ...))
   (((a = true) (c = const) ...) ...
    ((a = false) (c = const) ...) ...
    ((a = ⊥) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-con (b ...)))])

(define-metafunction classical
  all-class : P -> (((a = const) ...) ...)
  [(all-class ((a = p) ...))
   (get-vals-class
    ,(sort
      (remove-duplicates
       (remove* (term (a ...))
                (term (b ... ...))))
      a<))
          
   (where ((b ...) ...)
          ((vars p) ...))])

(define (a< x y)
  ((term-match/single
    evalu
    [(a* b*)
     (symbol<? (term a*) (term b*))]
    [((+ a*) (- a*))
     #t]
    [((- a*) (+ a*))
     #f]
    [((ann_1 a*) (ann_2 b*))
     (symbol<? (term a*) (term b*))])
   (list x y)))

(define-metafunction classical
  get-vals-class : (a ...) -> (((a = const) ...) ...)
  ;; expects inputs sorted by `a<`
  [(get-vals-class ()) (())]
  [(get-vals-class ((+ a*) (- a*) b ...))
   ((((+ a*) = false) ((- a*) = false) (c = const) ...) ...
    (((+ a*) = true) ((- a*) = false) (c = const) ...) ...
    (((+ a*) = false) ((- a*) = true) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-class (b ...)))]
  [(get-vals-class (a b ...))
   (((a = true) (c = const) ...) ...
    ((a = false) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-class (b ...)))])


(define-extended-language evalu classical
  [const ::= .... ⊥]
  [env ::= ((a = const) ...)]
  [E ::=
     (unevalable ... (a = E*) e ...)]
  [unevalable ::=
              (p = const)
              (p = unevalable-p)]
  [unevalable-p ::=
              a
              (or ⊥ unevalable-p)
              (or unevalable-p ⊥)
              (or unevalable-p unevalable-p)
              (and unevalable-p unevalable-p)
              (and ⊥ unevalable-p)
              (and unevalable-p ⊥)
              (not unevalable-p)]
  [v ::= const unevalable-p]
  [E* ::=
      hole
      (and E* p)
      (and v E*)
      (or E* p)
      (or v E*)
      (not E*)])


(define-metafunction evalu
  vars : p -> (a ...)
  [(vars (and p q))
   (a ... b ...)
   (where (a ...) (vars p))
   (where (b ...) (vars q))]
  [(vars (or p q))
   (a ... b ...)
   (where (a ...) (vars p))
   (where (b ...) (vars q))]
  [(vars (not p)) (vars p)]
  [(vars a) (a)]
  [(vars const) ()])

(define-metafunction evalu
  eval-con : P ((a = const) ...) -> ((unevalable ...) ...)
  [(eval-con P ((a = const) ...))
   ,(apply-reduction-relation* ->b (term (replace* P (a const) ...)))])

(define-metafunction evalu
  eval-clas : P ((a = const) ...) -> ((unevalable ...) ...)
  [(eval-clas P ((a = const) ...))
   ,(apply-reduction-relation* ->b (term (replace* P (a const) ...)))])



(define ->b
  (reduction-relation
   evalu
   #:domain P
   ;; and
   [-->
    (in-hole E (and true p))
    (in-hole E p)
    and-1-left]
   [-->
    (in-hole E (and p true))
    (in-hole E p)
    and-1-right]
   [-->
    (in-hole E (and false p))
    (in-hole E false)
    and-0-left]
   [-->
   (in-hole E (and p false))
    (in-hole E false)
    and-0-right]
   [-->
    (in-hole E (and ⊥ ⊥))
    (in-hole E ⊥)
    and-⊥]
   ;; or
   [-->
    (in-hole E (or true p))
    (in-hole E true)
    or-1-left]
   [-->
    (in-hole E (or p true))
    (in-hole E true)
    or-1-right]
   [-->
    (in-hole E (or false p))
    (in-hole E p)
    or-0-left]
   [-->
    (in-hole E (or p false))
    (in-hole E p)
    or-0-right]
   [-->
    (in-hole E (or ⊥ ⊥))
    (in-hole E ⊥)
    or-⊥]
   ;; not
   [-->
    (in-hole E (not true))
    (in-hole E false)
    not-1]
   [-->
    (in-hole E (not false))
    (in-hole E true)
    not-0]
   [-->
    (in-hole E (not ⊥))
    (in-hole E ⊥)
    not-⊥]
   ;; update-envs
   [-->
    (unevalable ...)
    (replace*
     (unevalable ...)
     (c_1 const_1)
     (c const) ...)
    (where
     ((c_1 = const_1)
      (c = const) ...)
     (consts-of (unevalable ...)))
    (side-condition
     (not
      (equal?
       (term (unevalable ...))
       (term
        (replace*
         (unevalable ...)
         (c_1 const_1)
         (c const) ...)))))
    update-env]))

(module+ test
  (check-equal?
   (remove-duplicates
    (apply-reduction-relation*
     ->b
     (term ((x = (or true false))))))
   (term (((x = true)))))

  (check-equal?
   (remove-duplicates
    (apply-reduction-relation*
     ->b
     (term
      (((+ left) = (or true (+ lem)))
       ((+ lem) = (and false (and false true)))))))
   (term
    ((((+ left) = true)
      ((+ lem) = false))))))

(define-metafunction evalu
  consts-of : P -> env
  [(consts-of ()) ()]
  [(consts-of ((a = const) (b = p) ...))
   ((a = const) (c = const_1) ...)
   (where ((c = const_1) ...)
          (consts-of ((b = p) ...)))]
  [(consts-of ((a = q) (b = p) ...))
   (consts-of ((b = p) ...))])


;                                                                                  
;                                                                                  
;                                                        ;;                        
;    ;;;;;;                                    ;         ;;                        
;    ;                                         ;                  ;;               
;    ;                                         ;                  ;;               
;    ;          ;;; ;    ;    ;    ;;;;;       ;       ;;;;     ;;;;;;    ;;    ;; 
;    ;         ;;  ;;    ;    ;        ;       ;          ;       ;;      ;;    ;  
;    ;        ;;    ;    ;    ;        ;;      ;          ;       ;;       ;   ;;  
;    ;;;;;    ;;    ;    ;    ;     ;;;;;      ;          ;       ;;       ;   ;   
;    ;        ;;    ;    ;    ;    ;   ;;      ;          ;       ;;       ;;  ;   
;    ;        ;;    ;    ;    ;   ;;   ;;      ;          ;       ;;        ;  ;   
;    ;        ;;    ;    ;    ;   ;;   ;;      ;          ;       ;;        ; ;    
;    ;         ;;  ;;    ;   ;;   ;;  ;;;      ;          ;       ;;  ;     ;;;    
;    ;;;;;;     ;;; ;    ;;;; ;    ;;;; ;       ;;;    ;;;;;;      ;;;;      ;;    
;                   ;                                                        ;     
;                   ;                                                        ;     
;                   ;                                                      ;;      
;                                                                         ;        
;                                                                                  


(define-metafunction classical
  get-constructive-expression : P -> p
  [(get-constructive-expression ((a = p) ...))
   (get-constructive-expression-acc (c ...) (c ...) true)
   (where ((b ...) ...) ((vars p) ...))
   (where (c ...) ,(remove-duplicates (term (a ... b ... ...))))])

(module+ test
  (check-equal?
   (term (get-constructive-expression
          (convert-P
           ((a = b)
            (b = c)))))
   (term (and (or (+ c) (- c))
              (and (or (+ b) (- b))
                   (and (or (+ a) (- a))
                        true))))))

(define-metafunction classical
  ;; initial-P P-recured-over accumulator
  get-constructive-expression-acc : (a ...) (a ...) p -> p
  [(get-constructive-expression-acc (a ...) () p) p]
  [(get-constructive-expression-acc (a ...) ((+ a*) b ...) p)
   (get-constructive-expression-acc
    (a ...) (b ...)
    (and (get-constructive-expression-for (a ...) a*) p))
   (side-condition/hidden (term (check-for-pos-neg! (a ...) a*)))]
  [(get-constructive-expression-acc (a ...) ((- a*) b ...) p)
   (get-constructive-expression-acc
    (a ...) (b ...)
    p)
   (side-condition/hidden (term (check-for-pos-neg! (a ...) a*)))])

(define-metafunction classical
  check-for-pos-neg! : (a ...) a* -> #t
  [(check-for-pos-neg! (a ...) a*)
   #t
   (where (_ ... (+ a*) _ ...) (a ...))
   (where (_ ... (- a*) _ ...) (a ...))]
  [(check-for-pos-neg! (a ...) a*)
   ,(error 'assert-same
           "checking constructiveness cannot be performed because ~a does not have a positive and negative part\nin: ~a"
           (term a*)
           (pretty-format (term (a ...))))])

(define-metafunction classical
  get-constructive-expression-for : (a ...) a* -> p
  [(get-constructive-expression-for (a ...) a*)
   (or (+ a*) (- a*))
   (side-condition/hidden (term (check-for-pos-neg! (a ...) a*)))])

(define (get-constructive-checked-form p q)
  (define constructive?-name
    (variable-not-in (list p q)
                     'constructive?))
  (define con? (redex-match? constructive P p))
  (define p*
    (let ([n (if con? (term (convert-P ,p)) p)])
      (term
       (,@n
        (,constructive?-name = (get-constructive-expression ,n))))))
  (define q*
    (let ([n (if con? (term (convert-P ,q)) q)])
      (term
       (,@n
        (,constructive?-name = (get-constructive-expression ,n))))))
  (log-circuits-debug "p = ~a" (pretty-format p*))
  (log-circuits-debug "q = ~a" (pretty-format q*))
  (values p* q*))

(define (assert-same/smt p q
                         #:constraints [constraints `true]
                         #:outputs [outputs #f])
  (define x
    (verify-same p q
                 #:constraints constraints
                 #:outputs outputs))
  (unless (unsat? x)
    (match-define (list sat p1 q1) x)
    (define the-diff
      (for*/list ([l (in-list p1)]
                  [r (in-list q1)]
                  #:when (and (equal? (first l) (first r))
                              (not (equal? (second l) (second r)))))
        (list l r)))
    (error 'assert-same
           "rosette model gave counterexample:\n~a\n~a\n~a\n~a"
           (pretty-format sat)
           (pretty-format the-diff)
           (pretty-format p1)
           (pretty-format q1))))

(define (assert-same p q)
  (define-values (p* q*)
    (get-constructive-checked-form p q))
  (define res
    (term (interp-both-class ,p* ,q*)))
  (define res*
    (for*/list ([x (in-list res)]
                [y (in-value
                    (first-is-not-superset (term (unknownify ,(second x)))
                                           (term (unknownify ,(third x)))))]
                #:when y)
      (cons y x)))
  
  (unless (empty? res*)
    (error 'equal-class
           "the diff:\n ~a"
           (pretty-format res*))))

(define (first-is-not-superset a b)
  (and (not (empty? b))
       (for/or ([x (in-list b)])
         (and (not
               (for/or ([y (in-list a)]
                        #:when (equal? x y))
                 #t))
              (list "a broken clause:" x)))))

(define-metafunction evalu
  unknownify : P -> ((a = const) ...)
  [(unknownify (e ...)) ((unknownify-e e) ...)])
(define-metafunction evalu
  unknownify-e : e -> (a = const)
  [(unknownify-e (a = const)) (a = const)]
  [(unknownify-e (a = _)) (a = false)])


                

;                                                                                                                           
;                                                                                                                           
;                                                                                                                           
;                         ;;;;;      ;;;;;                                                                              ;;  
;  ;;       ;;               ;;         ;;                  ;;;;;;;;                                                    ;;  
;  ;;       ;                ;;         ;;                  ;;                                                          ;;  
;  ;;  ;;;  ;                ;;         ;;                  ;;                                                          ;;  
;   ;  ;;;  ;     ;;;;       ;;         ;;                  ;;          ;;;;      ;;; ;;;;  ; ;;  ;;      ;;;;      ;;;;;;  
;   ;  ; ;  ;   ;;   ;;      ;;         ;;                  ;;         ;;   ;;     ;;;; ;   ;; ;;; ;;   ;;   ;;    ;;  ;;;  
;   ;  ; ;  ;   ;     ;      ;;         ;;                  ;;         ;    ;;     ;;;  ;   ;   ;  ;;   ;     ;    ;    ;;  
;   ;  ; ; ;;   ;     ;      ;;         ;;                  ;;;;;;;   ;;     ;     ;;       ;   ;  ;;   ;     ;   ;;    ;;  
;   ;; ; ; ;;  ;;;;;;;;      ;;         ;;                  ;;        ;;     ;     ;;       ;   ;  ;;  ;;;;;;;;   ;;    ;;  
;   ;;;; ; ;   ;;            ;;         ;;                  ;;        ;;     ;     ;;       ;   ;  ;;  ;;         ;;    ;;  
;   ;;;  ;;;    ;            ;;         ;;                  ;;        ;;     ;     ;;       ;   ;  ;;   ;         ;;    ;;  
;   ;;;  ;;;    ;;           ;;         ;;                  ;;         ;    ;;     ;;       ;   ;  ;;   ;;         ;    ;;  
;    ;;   ;;    ;;;  ;;      ;;  ;      ;;  ;               ;;         ;;  ;;;     ;;       ;   ;  ;;   ;;;  ;;    ;;  ;;;  
;    ;;   ;;      ;;;;        ;;;;       ;;;;               ;;          ;;;;      ;;;;;     ;   ;  ;;     ;;;;      ;;;  ;  
;                                                                                                                           
;                                                                                                                           
;                                                                                                                           
;                                                                                                                           
;                                                                                                                           

(define-metafunction constructive
  well-formed : P -> boolean
  [(well-formed ()) #t]
  [(well-formed ((a = p) e ...))
   (well-formed (e ...))
   (where ((a_!_1 = p_1) (a_!_1 = p_2) ...)
          ((a = p) e ...))]
  [(well-formed P) #f])


;                                                    
;                                                    
;                                                    
;   ;;;;;;;;                                         
;      ;                            ;;               
;      ;                            ;;               
;      ;        ;;;;      ;;;;    ;;;;;;      ;;;;   
;      ;       ;;  ;;    ;    ;     ;;       ;    ;  
;      ;       ;    ;    ;          ;;       ;       
;      ;      ;;    ;    ;;         ;;       ;;      
;      ;      ;;;;;;;     ;;;;      ;;        ;;;;   
;      ;      ;;             ;;     ;;           ;;  
;      ;       ;              ;     ;;            ;  
;      ;       ;;   ;   ;;   ;;     ;;  ;   ;;   ;;  
;      ;        ;;;;     ;;;;;       ;;;;    ;;;;;   
;                                                    
;                                                    
;                                                    
;                                                    
;                                                    


(module+ test
  (define (map-conv x)
    (map (lambda (x) (term (convert-P ,x)))
         x))
  (check-equal?
   (list->set (term (interp-con ((a = b)))))
   (set (term ((a = true)))
        (term ((a = false)))
        (term ((a = ⊥)))))
  (check-equal?
   (list->set (term (interp-class ((a = b)))))
   (set (term ((a = true)))
        (term ((a = false)))))
  (check-equal?
   (list->set (term (interp-class (convert-P ((a = b))))))
   (set (term (((+ a) = false) ((- a) = false)))
        (term (((+ a) = true) ((- a) = false)))
        (term (((+ a) = false) ((- a) = true)))))
  (check-equal?
   (apply-reduction-relation*
    ->b
    (term
     ((K0 = (and left (and right both)))
      (right = (or true rem)))))
   (term
    (((K0 = (and left both))
      (right = true)))))
  (test-begin
   (check-equal?
    (list->set (map-conv (term (interp-con ((a = (and true true)))))))
    (list->set (term (interp-class (convert-P ((a = (and true true))))))))
   (let ()
     (define-term s
       ((K0 = (and left (and right both)))
        (left = (or l0 lem))
        (right = (or r0 rem))
        (l0 = GO)
        (lem = (not (or GO false)))
        (rem = (not (or GO sel)))
        (both = (or l0 r0))))
     (check-equal?
      (list->set (map-conv (term (interp-con s))))
      (list->set (term (interp-class (convert-P s))))))
   (redex-check
    constructive
    P
    (equal?
     (list->set (map-conv (term (interp-con P))))
     (list->set (term (interp-class (convert-P P)))))))
  (check-not-exn
   (lambda ()
     (assert-same
      (term ((a = b) (b = c)))
      (term ((a = c))))))
  (check-not-exn
   (lambda ()
     (assert-same/smt
      (term ((a = b) (b = c)))
      (term ((a = c))))))
  (check-not-exn
   (lambda ()
     (assert-same
      (term (convert-P ((a = b) (b = c))))
      (term (convert-P ((a = c)))))))
  (check-not-exn
   (lambda ()
     (assert-same/smt
      (term (convert-P ((a = b) (b = c))))
      (term (convert-P ((a = c)))))))
  (check-exn
   #rx"the diff"
   (lambda ()
     (assert-same (term ((a = b)))
                  (term ((a = true))))))
  (check-exn
   #rx"assert-same.*model"
   (lambda ()
     (assert-same/smt (term ((a = b)))
                      (term ((a = true))))))
  (check-exn
   #rx"the diff"
   (lambda ()
     (assert-same
      (term ((a = b) (b = c)))
      (term ((a = true))))))
  (check-exn
   #rx"assert-same.*model"
   (lambda ()
     (assert-same/smt
      (term ((a = b) (b = c)))
      (term ((a = true))))))
  (check-exn
   #rx"the diff"
   (lambda ()
     (assert-same
      (term (convert-P ((a = b) (b = c))))
      (term (convert-P ((a = true)))))))
  (check-exn
   #rx"assert-same.*model"
   (lambda ()
     (assert-same/smt
      (term (convert-P ((a = b) (b = c))))
      (term (convert-P ((a = true)))))))
  (check-exn
   #rx"the diff"
   (lambda ()
     (assert-same
      (term ((SEL = reg-out)
             (k2 = GO)
             ))
      (term
       ((SEL = false)
        (k2 = GO)
        )))))
  (check-exn
   #rx"assert-same.*model"
   (lambda ()
     (assert-same/smt
      (term ((SEL = reg-out)
             (k2 = GO)
             ))
      (term
       ((SEL = false)
        (k2 = GO)
        )))))
  (test-case "constructivity vs classical tests"
    (test-case "postive/negative part check"
      (check-exn
       #rx"z does not have a positive and negative part"
       (lambda ()
         (assert-same
          (term
           (((+ z) = true)))
          (term ())))))
    (test-case "postive/negative part check"
      (check-exn
       #rx"z does not have a positive and negative part"
       (lambda ()
         (assert-same
          (term
           (((- z) = true)))
          (term ())))))
    (test-case "Initial example of constructive vs classical from Malik 1994"
      (check-exn
       #rx"the diff"
       (lambda ()
         (assert-same
          (term
           ((z = (and x a))
            (a = (or x a))))
          (term ((z = x))))))
      (check-exn
       #rx"assert-same.*model"
       (lambda ()
         (assert-same/smt
          (term
           ((z = (and x a))
            (a = (or x a))))
          (term ((z = x)))))))
    (test-case "empty circuit is always constructive"
      (check-exn
       #rx"the diff"
       (lambda ()
         (assert-same
          (term ((a = a)))
          (term ()))))
      (check-exn
       #rx"assert-same.*model"
       (lambda ()
         (assert-same/smt
          (term ((a = a)))
          (term ()))))
      (check-exn
       #rx"the diff"
       (lambda ()
         (assert-same
          (term ((a = b)
                 (b = a)))
          (term ()))))
      (check-exn
       #rx"assert-same.*model"
       (lambda ()
         (assert-same/smt
          (term ((a = b)
                 (b = a)))
          (term ())))))
    (test-case "a cycle is never constructive"
      (check-not-exn
       (lambda ()
         (assert-same
          (term ((a = a)))
          (term ((a = ⊥))))))
      (check-not-exn
       (lambda ()
         (assert-same/smt
          (term ((a = a)))
          (term ((a = ⊥))))))))
  (test-case "pinning tests"
    (let ()
      (define p1
        (term
         (
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
      (define p2 (term ((K0 = r0) (SEL = rsel))))
      (check-exn
       #rx"assert-same.*model"
       (lambda () (assert-same/smt p1 p2)))))
      
           
  (redex-check
   constructive
   P
   (begin
     (when (term (well-formed P))
       (assert-same (term P) (term P))
       (assert-same/smt (term P) (term P))
       (assert-same/smt (term (convert-P P))
                        (term (convert-P P)))))))