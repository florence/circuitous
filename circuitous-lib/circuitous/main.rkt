#lang racket/base
(require racket/contract
         redex/reduction-semantics
         "interp.rkt"
         "manipulations.rkt"
         (only-in "private/data.rkt"
                  circuit-domain
                  circuit-inputs
                  circuit-outputs
                  circuit?
                  variable<?)
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
        (#:constraints [e extended-boolean-expression/c])
        #:rest [_ (c) (listof (type c))]
        [result circuit?]
        #:post (c result e) (assert-same c result
                                         #:constraints
                                         (if (equal? e the-unsupplied-arg)
                                             'true
                                             e)))]))

(define (make-circuit #:inputs inputs
                      #:outputs outputs
                      #:register-pairs [reg-pairs empty]
                      expr)
  (apply make-circuitf
         #:inputs inputs
         #:outputs outputs
         reg-pairs
         expr))
         

(provide
 circuit
 unsat?
 sat?
 (contract-out
  [circuit? predicate/c]
  [variable/c flat-contract?]
  [boolean-expression/c flat-contract?]
  [circuit-inputs (-> circuit? (listof variable/c))]
  [circuit-outputs (-> circuit? (listof variable/c))]
  [circuit-domain (-> circuit? (listof variable/c))]
  [variable<? (-> variable/c variable/c boolean?)]
  [constructive-circuit? (-> circuit? any/c)]
  [classical-circuit? (-> circuit? any/c)]
  [make-circuit
   (->* (#:inputs (listof symbol?)
         #:outputs (listof symbol?)
         (listof (list/c symbol? '= boolean-expression/c)))
        (#:register-pairs (listof (list/c symbol? symbol?)))
        circuit?)]
  [link
   (->i ([a circuit?]
         #:with [b (a)
                   (and/c circuit? (same-circuit-as/c a))]
         #:inputs [inputs (listof (list/c variable/c variable/c))]
         #:outputs [outputs (listof (list/c variable/c variable/c))])
        #:pre (a b inputs outputs)
        (and (subset? (list->set (circuit-inputs b)) (list->set (map first inputs)))
             (subset? (list->set (circuit-outputs b)) (list->set (map first outputs))))
        [res (a)
             (and/c circuit? (same-circuit-as/c a))])]
  [propagate&remove
   (transformer-over/c
    (λ (c)
      (and/c variable/c
             (lambda (x) (member x (circuit-domain c))))))]
  [propagate
   (transformer-over/c
    (λ (c)
      (and/c variable/c
             (lambda (x) (member x (circuit-domain c))))))]
  [replace
   (transformer-over/c (lambda (_) (list/c boolean-expression/c boolean-expression/c)))]
  [rename rename rename ;; because it looks like contract-out looks for rename as a datum-literal :(
          (transformer-over/c (λ (_) (list/c variable/c variable/c)))]
  [constructive->classical
   (-> (and/c circuit? constructive-circuit?)
       classical-circuit?)]
  [execute (->i ([c circuit?])
                #:rest [inputs () (listof (listof (list/c variable/c (or/c 'true 'false #f #t))))]
                #:pre (c inputs)
                (for/and ([i (in-list inputs)])
                  (equal? (list->set (map first i))
                          (list->set (circuit-inputs c))))
                [_ (listof (listof (list/c variable/c any/c)))])]
  [assert-same (->i ([p circuit?]
                     [q (p) (and/c circuit? (same-circuit-as/c p))])
                    (#:constraints [c extended-boolean-expression/c])
                    #:pre
                    (p q)
                    (and (distinct? (circuit-inputs p) (circuit-outputs q))
                         (distinct? (circuit-inputs q) (circuit-outputs p)))
                    any)]
  [verify-same (->i ([p circuit?]
                     [q (p) (and/c circuit? (same-circuit-as/c p))])
                    (#:constraints [c extended-boolean-expression/c])
                    #:pre
                    (p q)
                    (and (distinct? (circuit-inputs p) (circuit-outputs q))
                         (distinct? (circuit-inputs q) (circuit-outputs p)))
                    [_ (or/c unsat?
                             (list/c sat?
                                     (listof (listof (list/c variable/c any/c)))
                                     (listof (listof (list/c variable/c any/c)))))])]))
