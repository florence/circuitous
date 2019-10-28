#lang rosette/safe
(provide interp@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match
         (for-syntax syntax/parse)
         (only-in racket/base error
                  define-logger))
(define-logger circuit-solver)
(define-logger circuit-eval)

(module+ test (require rackunit))


(define-syntax with-asserts*
  (syntax-parser
    [(_ b ...)
     #'(let-values ([(r _)
                     (with-asserts (let () b ...))])
         r)]))

(define-unit interp@
  (import sem^)
  (export interp^)

  (define (eval state formulas)
    (define (eval* state formulas bound)
      (if (zero? bound)
          state
          (let ([x (step state formulas)])
            (eval* x formulas (sub1 bound)))))
    (eval* state formulas (interp-bound formulas)))

  (define (step state formulas)
    (map 
     (lambda (w)
       (define name (first w))
       (define f
         (and (contains? formulas name)
              (deref formulas name)))
       (if f
           (list name (f state))
           w))
     state))

  (define (eval/multi states formulas in-registers out-registers)
    (log-circuit-eval-debug "starting eval/multi")
    (reverse
     (let loop ([registers out-registers]
                [seen (list)]
                [states states])
       (log-circuit-eval-debug "states: ~a" (pretty-format states))
       (log-circuit-eval-debug "seen: ~a" (pretty-format seen))
       (log-circuit-eval-debug "registers: ~a" out-registers)
       (cond
         [(empty? states) seen]
         [else
          (define next (eval (append (first states) registers)
                             formulas))
          (log-circuit-eval-debug "next: ~a" (pretty-format next))
          (if (not (constructive? next))
              (cons next seen)
              (loop (map (lambda (in outpair)
                           (list (first outpair)
                                 (deref next in)))
                         in-registers
                         out-registers)
                    (cons next seen)
                    (rest states)))]))))
  (define (eval/multi* IVS eqs register-pairs)
    (define mid (build-state eqs (list)))
    (eval/multi (map (lambda (x) (append x mid)) IVS)
                (build-formula eqs)
                (map first register-pairs)
                (initialize-to-false
                 (map second register-pairs))))

  (define (result=? a b #:outputs [outputs #f])
    (and
     (outputs=? a b #:outputs outputs)
     (equal? (constructive? a)
             (constructive? b))))

  (define (result=?/multi a b #:outputs [outputs #f])
    (and
     (equal? (length a) (length b))
     (let andmap ([a a]
                  [b b])
       (if (empty? a)
           #t
           (and (result=? (first a) (first b) #:outputs (or outputs #f))
                (andmap (rest a) (rest b)))))))

  (define (verify-same P1 P2
                       #:register-pairs1 [register-pairs1 #f]
                       #:register-pairs2 [register-pairs2 #f]
                       #:constraints [extra-constraints 'true]
                       #:outputs [outputs #f])
    (log-circuit-solver-debug
     "P1: ~a" (pretty-format P1))
    (log-circuit-solver-debug
     "P2: ~a" (pretty-format P2))
    (cond
      [(and register-pairs1 register-pairs2)
       (verify-same/multi P1 P2
                          #:register-pairs1 register-pairs1
                          #:register-pairs2 register-pairs2
                          #:constraints extra-constraints
                          #:outputs outputs)]
      [(not (or register-pairs1 register-pairs2))
       (verify-same/single P1 P2
                           #:constraints extra-constraints
                           #:outputs outputs)]
      [else (error "missing register pair set")]))
  (define (verify-same/multi P1 P2
                             #:register-pairs1 [register-pairs1 (list)]
                             #:register-pairs2 [register-pairs2 (list)]
                             #:constraints [extra-constraints 'true]
                             #:outputs [outputs #f])
    (do-verify
     #:=? result=?/multi
     #:expr1 e1
     #:expr2 e2
     #:given-constraints const
     #:gened-constraints extra
     #:outputs outputs
     
     (log-circuit-solver-debug "starting multi run for\n~a\nand\n~a"
                               (pretty-format P1)
                               (pretty-format P2))
     (define register-ins1 (map first register-pairs1))
     (define register-outs1 (map second register-pairs1))
     (define register-ins2 (map first register-pairs2))
     (define register-outs2 (map second register-pairs2))
     (define maximal-statespace
       (max (get-maximal-statespace (length register-pairs1))
            (get-maximal-statespace (length register-pairs2))))
     (log-circuit-solver-debug "maximal-statespace: ~a" maximal-statespace)
     (define inputs1+2
       (let loop ([x maximal-statespace])
         (cond [(zero? x) (list (list) (list))]
               [else
                (define inputs1+2
                  (symbolic-inputs P1 P2 #:exclude (append register-outs1 register-outs2)))
                (define r1+2 (loop (sub1 x)))
                (list (cons (first inputs1+2) (first r1+2))
                      (cons (second inputs1+2) (second r1+2)))])))
     (define inputs1 (first inputs1+2))
     (define inputs2 (second inputs1+2))
     (log-circuit-solver-debug "inputs1: ~a" (pretty-format inputs1))
     (log-circuit-solver-debug "inputs2: ~a" (pretty-format inputs2))
     (define e1
       (symbolic-repr-of-eval/multi inputs1 P1 register-pairs1))
     (define e2
       (symbolic-repr-of-eval/multi inputs2 P2 register-pairs2))
     (define (make-extra e)
       (andmap
        (lambda (v) (equal? #t ((build-expression extra-constraints) v)))
        e))
     (define (make-c e)
       (andmap
        (lambda (v) (equal? #t (constraints v)))
        e))
     (define (build-extra ea eb in o)
       (let loop
         ([ea ea]
          [in in])
         (if (empty? ea)
             (list)
             (cons (append (first ea) (first in) (initialize-to-false (or o (map first (first eb)))))
                   (loop (rest ea) (rest in))))))
     (define extra
       (and (make-extra (build-extra e1 e2 inputs2 outputs))
            (make-extra (build-extra e2 e1 inputs1 outputs))))
     (define const
       (and (make-c e1)
            (make-c e2)))))
  (define (totally-constructive? p
                                 #:register-pairs [rp (list)]
                                 #:constraints [c 'true])
    (define r 
      (verify-same/multi p (list)
                         #:register-pairs1 rp
                         #:register-pairs2 (list)
                         #:outputs (list)
                         #:constraints
                         `(and ,(constructive-constraints p) ,c)))
    (if (unsat? r)
        r
        (take r 2)))
  (define (verify-same/single P1 P2
                              #:constraints [extra-constraints 'true]
                              #:outputs [outputs #f])
    (do-verify
     #:=? result=?
     #:expr1 e1
     #:expr2 e2
     #:given-constraints const
     #:gened-constraints extra
     #:outputs outputs
     (define inputs1+2 (symbolic-inputs P1 P2))
     (define inputs1 (first inputs1+2))
     (define inputs2 (second inputs1+2))
     (log-circuit-solver-debug "inputs1: ~a" (pretty-format inputs1))
     (log-circuit-solver-debug "inputs2: ~a" (pretty-format inputs2))
     (log-circuit-solver-debug "extras: ~a" (pretty-format extra-constraints))
     (define e1 (symbolic-repr-of-eval P1 inputs1))
     (define e2 (symbolic-repr-of-eval P2 inputs2))
     (define (make-extra e)
       (equal? #t ((build-expression extra-constraints) e)))
     (define (make-c e)
       (equal? #t (constraints e)))
     (define (build-extra ea eb in o)
       (append ea in (initialize-to-false (or o (map first eb)))))
     (define extra
       (and (make-extra (build-extra e1 e2 inputs2 outputs))
            (make-extra (build-extra e2 e1 inputs1 outputs))))
     (define const
       (and (make-c e1)
            (make-c e1)))))
  
  (define-syntax do-verify
    (syntax-parser
      [(_ #:=? =?:id
          #:expr1 e1:id
          #:expr2 e2:id
          #:given-constraints given-constraints:id
          #:gened-constraints gened-constraints:id
          #:outputs outputs:id
          body:expr ...)
       #'(with-asserts*
          body ...
          (verify/f =? e1 e2 given-constraints gened-constraints outputs))]))
  
  (define (verify/f =? e1 e2 given-constraints gened-constraints outputs)
    (log-circuit-solver-debug "e1: ~a" (pretty-format e1))
    (log-circuit-solver-debug "e1 vars: ~a" (pretty-format (symbolics e1)))
    (log-circuit-solver-debug "e2: ~a" (pretty-format e2))
    (log-circuit-solver-debug "e2 vars: ~a" (pretty-format (symbolics e2)))
    (log-circuit-solver-debug "constraints: ~a" (pretty-format (equal? #t given-constraints)))
    (log-circuit-solver-debug "generated constraints: ~a" (pretty-format (equal? #t gened-constraints)))
    (log-circuit-solver-debug "asserts: ~a" (pretty-format (asserts)))

    (define eq (equal? #t (=? e1 e2 #:outputs outputs)))
    
    (log-circuit-solver-debug "eq: ~a" (pretty-format eq))
    (log-circuit-solver-debug "eq symbolics: ~a" (pretty-format (symbolics eq)))
    (define r
      (verify
       ;; note: this assumes that
       ;; the constraints require strict truth
       ;; not not-falseness
       #:assume (assert (and (equal? #t given-constraints)
                             (equal? #t gened-constraints)))
       #:guarantee (assert eq)))
    (when (sat? r)
      (log-circuit-solver-debug
       "symbolics in result: ~a"
       (pretty-format
        (map
         (lambda (x) (list x (r x)))
         (symbolics eq)))))
    (if (unsat? r)
        r
        (let ([r (complete-solution r (symbolics eq))])
          (list r (evaluate e1 r) (evaluate e2 r)))))
  
  (define (symbolic-repr-of-eval/multi inputs P register-pairs)
    (eval/multi* inputs
                P
                register-pairs))
  (define (symbolic-repr-of-eval P inputs)
    (eval (build-state P inputs)
          (build-formula P)))

  (define (build-formula P)
    (map
     (lambda (x)
       (match-define (list n '= e) x)
       (list n (build-expression e)))
     P))
  (define (build-state P inputs)
    (append
     (map
      (lambda (w) (list (first w) initial-value))
      P)
     inputs))

  (define (build-expression e)
    (match e
      [`(and ,e1 ,e2)
       (f-and (build-expression e1)
              (build-expression e2))]
      [`(or ,e1 ,e2)
       (f-or (build-expression e1)
             (build-expression e2))]
      [`(not ,e1)
       (f-not (build-expression e1))]
      [`(implies ,e1 ,e2)
       (f-implies (build-expression e1)
                  (build-expression e2))]
      [(or #t `true) (lambda (_) #t)]
      [(or #f `false) (lambda (_) #f)]
      [`⊥ (lambda (_) '⊥)]
      [x
       (lambda (w) (deref w x))]))

  
  (define (symbolic-inputs P1 P2 #:exclude [exclude (list)])
    (define (keep? x)
      (not (member x exclude)))
    (define FV1 (filter keep? (FV P1)))
    (define FV2 (filter keep? (FV P2)))
    (define shared
      (remove* (remove* FV1 FV2) FV2))
    (define (new-row x)
      (list x (symbolic-boolean x)))
    (define shared-symbolics
      (map new-row shared))
    (define (maybe-new-row x)
      (or (assoc x shared-symbolics)
          (new-row x)))
    (list
     (map maybe-new-row FV1)
     (map maybe-new-row FV2))))

(define (FV P)
  (remove-duplicates
   (remove* (map first P)
            (vars P))))

(define (vars P)
  (append-map get-vars (map third P)))
(define (get-vars e)
  (match e
    [`(and ,e1 ,e2)
     (append (get-vars e1) (get-vars e2))]
    [`(or ,e1 ,e2)
     (append (get-vars e1) (get-vars e2))]
    [`(not ,e1)
     (get-vars e1)]
    [`true (list)]
    [`false (list)]
    [`⊥ (list)]
    [x
     (list x)]))
    