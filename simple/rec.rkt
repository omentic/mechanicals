#lang racket
(require "../lib.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus with iso-recursive types

;; Checks an expression for syntactic well-formedness.
(define (stlc-rec/expr? expr)
  (match expr
    [x #:when (symbol? x) #t]
    [(or `(fold ,e) `(unfold ,e)) (stlc-rec/expr? e)]
    [`(,e1 ,e2) (and (stlc-rec/expr? e1) (stlc-rec/expr? e2))]
    [`(λ (,x : ,t) ,e) (and (symbol? x) (stlc-rec/type? t) (stlc-rec/expr? e))]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
(define (stlc-rec/type? type)
  (match type
    [t #:when (symbol? t) #t]
    [`(,t1 → ,t2) (and (stlc-rec/type? t1) (stlc-rec/type? t2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc-rec/value? value)
  (match value
    [x #:when (symbol? x) #t]
    [`(,v1 ,v2) (and (stlc-rec/value? v1) (stlc-rec/value? v2))]
    [`(λ ,x ,e ,env) (and (symbol? x) (stlc-rec/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define (interpret expr)
  (interpret/core (desugar expr) #hash()))
(define/contract (interpret/core expr Γ)
  (-> stlc-rec/expr? dict? stlc-rec/value?)
  (match expr
    ['sole 'sole]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [n #:when (natural? n) n]
    [f #:when (symbol? f) f]

    [`(fold ,e) `(fold ,(interpret/core e Γ))]
    [`(unfold ,e)
      (match (interpret/core e Γ)
        [`(fold ,e) e]
        [e `(unfold e)])]

    [`(λ (,x : ,t) ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret/core e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret/core e (dict-set env x (interpret/core e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]))

;; Checks an expression against some type, in a given context.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ)
  (-> stlc-rec/expr? stlc-rec/type? dict? boolean?)
  (match expr
    [`(fold (μ ,x ,t) ,e)
      (match with
        [`(μ ,x ,t) (check/core e t (dict-set Γ x `(μ ,x ,t)))]
        [_ #f])]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t1 t) (check/core e t2 (dict-set Γ x t1)))]
        [_ #f])]

    [_ (equal? (infer/core expr Γ) with)]))

;; Infers a type from some expression, in a given context.
(define (infer expr)
  (infer/core (desugar expr) #hash()))
(define/contract (infer/core expr Γ)
  (-> stlc-rec/expr? dict? stlc-rec/type?)
  (match expr
    ['sole 'Unit]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]
    [b #:when (boolean? b) 'Bool]
    [n #:when (natural? n) 'Nat]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]

    [`(fold (μ ,x ,t) ,e)
      (if (check/core e t (dict-set Γ x `(μ ,x ,t))) `(μ ,x ,t)
        (err (format "expected ~a to be of type ~a, got ~a"
          e t (infer e (dict-set Γ x `(μ ,x ,t))))))]
    [`(unfold (μ ,x ,t) ,e)
      (if (check/core e `(μ ,x ,t)) (replace t x `(μ ,x ,t))
        (err (format "expected ~a to be of type ~a, got ~a"
          e `(μ ,x ,t) (infer/core e Γ))))]

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer/core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(,t1 → ,t2)
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]))

;; Replace all references to an expression with a value.
(define (replace expr key value)
  (match expr
    ; do not accidentally replace shadowed bindings
    [(or `(λ (,x : ,_) ,_) `(λ ,x ,_) `(μ ,x ,_)
      `(type ,x ,_ ,_)) #:when (equal? x key) expr]
    [`(,e ...) `(,@(map (λ (x) (replace x key value)) e))]
    [x #:when (equal? x key) value]
    [v v]))
