#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus, with general recursion

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr)
  (interpret-core (strip (desugar expr)) #hash()))
(define (interpret-core expr Γ)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(fix ,e)
      (match (interpret-core e Γ)
        [`(λ ,x ,e ,env)
          ; FIXME: unsure what should be Γ and what should be env
          (interpret-core e (dict-set Γ x `(fix (λ ,x ,e ,Γ))))]
        [e (err (format "applying fix to unknown expression ~a" e))])]

    [`(λ ,id ,body) `(λ ,id ,body ,Γ)]
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]
    [`(,body ,arg)
      (match (interpret-core body Γ)
        [`(λ ,id ,body ,env)
          (interpret-core body (dict-set env id (interpret-core arg Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" arg e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (let ([with (if (dict-has-key? Γ with) (dict-ref Γ with) with)])
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [(`(fix ,e) with)
      (check-core (infer-core e) `(,with → ,with) Γ)]

    [(`(λ (,x : ,t) ,e) `(,t1 → ,t2))
      (and (equal? t t1) (check-core e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (and (equal? t2 t) (equal? t1 (infer-core e2 Γ)))]
        [t #f])]

    [(e t) #f])))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define (infer-core expr Γ)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(fix ,e)
      (match (infer-core e Γ)
        [`(,t → ,t) t]
        [t (err (format "fix expects a term of type t → t, got ~a" t))])]

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer-core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (if (check-core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "inferring an unknown expression ~a" e))]))
