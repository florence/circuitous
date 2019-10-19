#lang racket/base
(provide convert-P
         propigate/remove*
         propigate*
         rename*
         replace*
         rename*/freshen
         rename**
         replace-p*
         classical
         constructive)
(require redex/reduction-semantics
         racket/list)
(module+ test (require rackunit))

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
  rename** : P (a a) ... -> P
  [(rename** P) P]
  [(rename** P (a_1 a_2) (b_1 b_2) ...)
   (rename** (rename* P a_1 a_2)
             (b_1 b_2) ...)])


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
  replace-p* : (p ...) (p p) ... -> (p ...)
  [(replace-p* (p ...)) (p ...)]
  [(replace-p* (p ...)
               (p_1 p_2)
               (p_3 p_4) ...)
   (replace-p*
    ((replace-p p p_1 p_2) ...)
    (p_3 p_4) ...)])
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

(define-metafunction constructive
  rename*/freshen : ((a b) ...) P (a b) ... P -> (((a b) ...) P)
  [(rename*/freshen ((a_reg b_reg) ...) P (a b) ... P_i)
   (((a_regv b_regv) ...)
    (rename* P
             (a b) ...
             (a_v b_v) ...))
   (where (a_v ...)
          ,(remove*
            (term (a ...))
            (term (variables P))))
   (where (b_v ...)
          ,(variables-not-in
            (term (b ... P_i))
            (term (a_v ...))))
   (where ((a_regv = b_regv) ...)
          (rename* ((a_reg = b_reg) ...)
                   (a b) ...
                   (a_v b_v) ...)) ])
                             
  


(define-metafunction classical
  variables : P -> (a ...)
  [(variables (a = p) ...)
   ,(remove-duplicates (term (a ... b ... ...)))
   (where ((b ...) ...)
          ((vars-p p) ...))])

(define-metafunction classical
  vars-p : p -> (a ...)
  [(vars-p a) (a)]
  [(vars-p (_ p q))
   (a ... b ...)
   (where (a ...) (vars-p p))
   (where (b ...) (vars-p q))]
  [(vars-p (not p)) (vars-p p)]
  [(vars-p const) ()])