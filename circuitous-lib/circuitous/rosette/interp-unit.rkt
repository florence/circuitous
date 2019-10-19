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
            (if (equal? x state)
                state
                (eval* x formulas (sub1 bound))))))
    (eval* state formulas (length formulas)))

  (define (step state formulas)
    (map 
     (lambda (w)
       (match-define (list name v) w)
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
       (cond
         [(empty? states) seen]
         [else
          (define next (eval (append registers (first states))
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
     (define inputs
       (let loop ([x maximal-statespace])
         (if (zero? x)
             (list)
             (cons (symbolic-inputs (append P1 P2) #:exclude (append register-outs1 register-outs2))
                   (loop (sub1 x))))))
     (log-circuit-solver-debug "inputs: ~a" (pretty-format inputs))
     (define e1
       (symbolic-repr-of-eval/multi inputs P1 register-pairs1))
     (define e2
       (symbolic-repr-of-eval/multi inputs P2 register-pairs2))
     (define (make-extra e)
       (andmap
        (lambda (v) (equal? #t ((build-expression extra-constraints) v)))
        e))
     (define (make-c e)
       (andmap
        (lambda (v) (equal? #t (constraints v)))
        e))
     (define extra
       (and (make-extra e1)
            (make-extra e2)))
     (define const
       (and (make-c e1)
            (make-c e2)))))
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
     (define inputs (symbolic-inputs (append P1 P2)))
     (log-circuit-solver-debug "inputs: ~a" (pretty-format inputs))
     (log-circuit-solver-debug "extras: ~a" (pretty-format extra-constraints))
     (define e1 (symbolic-repr-of-eval P1 inputs))
     (define e2 (symbolic-repr-of-eval P2 inputs))
     (define (make-extra e)
       (equal? #t ((build-expression extra-constraints) e)))
     (define (make-c e)
       (equal? #t (constraints e)))
     (define extra
       (and (make-extra e1)
            (make-extra e2)))
     (define const
       (and (constraints e1)
            (constraints e1)))))
  
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
      [`true (lambda (_) #t)]
      [`false (lambda (_) #f)]
      [`⊥ (lambda (_) '⊥)]
      [x
       (lambda (w) (deref w x))]))

  (define (build-state P inputs)
    (append
     (map
      (lambda (w) (list (first w) '⊥))
      P)
     inputs))
  (define (symbolic-inputs P #:exclude [exclude (list)])
    (map
     (lambda (x) (list x (symbolic-boolean x)))
     (filter (lambda (x)
               (not (member x exclude)))
               (FV P)))))

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
    