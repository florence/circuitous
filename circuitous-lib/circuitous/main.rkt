#lang racket/base
(require racket/contract
         redex/reduction-semantics
         "interp.rkt"
         "manipulations.rkt"
         "private/data.rkt"
         "private/redex.rkt"
         "private/contract.rkt"
         racket/set
         racket/list 
         (only-in rosette unsat? sat?)
         (for-syntax syntax/parse racket/base))
         

(define-syntax transformer-over/c
  (syntax-parser
    [(_ type)
     #'(->i
        ([c circuit?])
        (#:constraints [e boolean-expression/c])
        #:rest [_ (listof type)]
        [result circuit?]
        #:post (c result) (assert-same c result #:contraints c))]))
   

(provide
 make-circuit
 unsat?
 sat?
 (contract-out
  [circuit? predicate/c]
  [variable/c flat-contract?]
  [boolean-expression/c flat-contract?]
  [circuit-inputs (-> circuit? (listof variable/c))]
  [circuit-outputs (-> circuit? (listof variable/c))]
  [constructive-circuit? (-> circuit? any/c)]
  [classical-circuit? (-> circuit? any/c)]
  [link
   (->i ([a circuit?]
         #:with [b (a)
                   (and/c circuit? (same-circuit-as/c a))]
         #:inputs [inputs (listof (list/c variable/c variable/c))]
         #:outputs [outputs (listof (list/c variable/c variable/c))])
        #:pre (a b inputs outputs)
        (and (equal? (list->set (circuit-inputs a) (list->set (map first inputs))))
             (equal? (list->set (circuit-inputs b) (list->set (map second inputs))))
             (equal? (list->set (circuit-outputs a) (list->set (map first outputs))))
             (equal? (list->set (circuit-outputs b) (list->set (map second outputs)))))
        [res (a)
             (and/c circuit? (same-circuit-as/c a))])]
  [propigate&remove
   (transformer-over/c variable/c)]
  [propigate
   (transformer-over/c variable/c)]
  [replace
   (transformer-over/c (list/c boolean-expression/c boolean-expression/c))]
  [rename rename rename ;; because it looks like contract-out looks for rename as a datum-literal :(
          (transformer-over/c (list/c variable/c variable/c))]
  [circuit->classical
   (-> (and/c circuit? constructive-circuit?)
       classical-circuit?)]
  [execute (->i ([c circuit?])
                #:rest [inputs () (listof (listof (list/c variable/c (or/c 'true 'false))))]
                #:pre (c inputs)
                (for/and ([i (in-list inputs)])
                  (equal? (list->set (map first i))
                          (list->set (circuit-inputs c))))
                (listof (list/c variable/c any/c)))]
  [assert-same (->i ([p circuit?]
                     [q (p) (and/c circuit? (same-circuit-as/c p))]
                     #:contraints [c boolean-expression/c])
                    any)]
  [verify-same (->i ([p circuit?]
                     [q (p) (and/c circuit? (same-circuit-as/c p))]
                     #:contraints [c boolean-expression/c])
                    [_ (or/c unsat?
                             (list/c sat?
                                     (listof (listof (list/c variable/c any/c)))
                                     (listof (listof (list/c variable/c any/c)))))])]))
