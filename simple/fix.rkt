#lang racket
(require "../lib.rkt")
(require (only-in "stlc.rkt" stlc/type?))

;; The Simply-Typed Lambda Calculus, with general recursion

;; Checks an expression for syntactic well-formedness.
(define/contract (stlc-fix/expr? expr)
  (-> any/c boolean?)
  (match expr
    [x #:when (symbol? x) #t]
    [`(fix ,e) (stlc-fix/expr? e)]
    [`(λ (,x : ,t) ,e) (and (symbol? x) (stlc/type? t) (stlc-fix/expr? e))]
    [`(,e1 ,e2) (and (stlc-fix/expr? e1) (stlc-fix/expr? e2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc-fix/value? value)
  (match value
    [x #:when (symbol? x) #t]
    [`(,v1 ,v2) (and (stlc-fix/value? v1) (stlc-fix/value? v2))]
    [`(λ ,x ,e ,env) (and (symbol? x) (stlc-fix/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define (interpret expr)
  (interpret/core (desugar expr) #hash()))
(define/contract (interpret/core expr Γ)
  (-> stlc-fix/expr? dict? stlc-fix/value?)
  (match expr
    ['sole 'sole]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [x #:when (symbol? x) x]

    [`(fix ,e)
      (match (interpret/core e Γ)
        [`(λ ,x ,e ,env)
          ; FIXME: unsure what should be Γ and what should be env
          (interpret/core e (dict-set env x `(fix (λ ,x ,e ,Γ))))]
        [e (err (format "applying fix to unknown expression ~a" e))])]

    [`(λ (,id : ,t) ,body) `(λ ,id ,body ,Γ)]
    [`(,body ,arg)
      (match (interpret/core body Γ)
        [`(λ ,id ,body ,env)
          (interpret/core body (dict-set env id (interpret/core arg Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" arg e))])]))

;; Checks an expression against some type, in a given context.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ) ; FIXME
  (-> stlc-fix/expr? stlc/type? dict? boolean?)
  (let ([with (if (dict-has-key? Γ with) (dict-ref Γ with) with)])
  (match expr
    [`(fix ,e)
      (check/core (infer/core e) `(,with → ,with) Γ)]
    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t1 t)
            (check/core e t2 (dict-set Γ x t1)))]
        [_ #f])]
    [_ (equal? (infer/core expr Γ) with)])))

;; Infers a type from some expression, in a given context.
(define (infer expr)
  (infer/core (desugar expr) #hash()))
(define/contract (infer/core expr Γ)
  (-> stlc-fix/expr? dict? stlc/type?)
  (match expr
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]
    [`(fix ,e)
      (match (infer/core e Γ)
        [`(,t → ,t) t]
        [t (err (format "fix expects a term of type t → t, got ~a" t))])]
    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer/core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(,t1 → ,t2)
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]))
