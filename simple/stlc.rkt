#lang racket
(require "../lib.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus

;; Checks an expression for syntactic well-formedness.
(define (stlc/expr? expr)
  (match expr
    [x #:when (symbol? x) #t]
    [`(,e1 ,e2) (and (stlc/expr? e1) (stlc/expr? e2))]
    [`(λ (,x : ,t) ,e) (and (symbol? x) (stlc/type? t) (stlc/expr? e))]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
(define (stlc/type? type)
  (match type
    [t #:when (symbol? t) #t]
    [`(,t1 → ,t2) (and (stlc/type? t1) (stlc/type? t2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc/value? value)
  (match value
    [x #:when (symbol? x) #t]
    [`(,v1 ,v2) (and (stlc/value? v1) (stlc/value? v2))]
    [`(λ ,x ,e ,env) (and (symbol? x) (stlc/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define/contract (interpret expr [Γ #hash()])
  (->* (stlc/expr?) (dict?) stlc/value?)
  (match expr
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f) f]
    [`(λ (,x : ,t) ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret e1 Γ)
        [`(λ ,x ,e ,env) (interpret e (dict-set env x (interpret e2 Γ)))]
        [e `(,e ,(interpret e2 Γ))])]))

;; Checks an expression against some type, in a given context.
(define/contract (check expr with [Γ #hash()])
  (->* (stlc/expr? stlc/type?) (dict?) boolean?)
  (match expr
    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t t1) (check e t2 (dict-set Γ x t)))]
        [_ #f])]
    [_ (equal? with (infer with Γ))]))

;; Infers a type from some expression, in a given context.
(define/contract (infer expr [Γ #hash()])
  (->* (stlc/expr?) (dict?) stlc/type?)
  (match expr
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]
    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer e1 Γ)
        [`(,t1 → ,t2)
          (if (check e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]))
