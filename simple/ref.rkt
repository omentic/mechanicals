#lang racket
(require "../lib.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus with references

; todo: rewrite to use call-by-reference or call-by-value or call-by-name explicitly

;; Checks an expression for syntactic well-formedness.
(define (stlc-ref/expr? expr)
  (match expr
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [(or `(new ,e) `(! ,e)) (stlc-ref/expr? e)]
    [(or `(set ,e1 ,e2) `(,e1 ,e2)) (and (stlc-ref/expr? e1) (stlc-ref/expr? e2))]
    [`(λ (,x : ,t) ,e) (and (symbol? x) (stlc-ref/type? t) (stlc-ref/expr? e))]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
(define (stlc-ref/type? type)
  (match type
    [t #:when (symbol? t) #t]
    [`(Ref ,t) (stlc-ref/type? t)]
    [`(,t1 → ,t2) (and (stlc-ref/type? t1) (stlc-ref/type? t2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc-ref/value? value)
  (match value
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [`(,v1 ,v2) (and (stlc-ref/value? v1) (stlc-ref/value? v2))]
    [`(λ ,x ,e ,env) (and (symbol? x) (stlc-ref/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define (interpret expr)
  (interpret/core (desugar expr) #hash() (make-hash)))
(define/contract (interpret/core expr Γ Σ)
  (-> stlc-ref/expr? dict? dict? stlc-ref/value?)
  (match expr
    [r #:when (dict-has-key? Σ r) r]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f) f]

    [`(new ,e)
      (let ([r (gensym)])
      (dict-set! Σ r e) r)]
    [`(! ,e)
      (let ([r (interpret/core e Γ Σ)])
      (if (dict-has-key? Σ r)
        (interpret/core (dict-ref Σ r) Γ Σ)
        (err (format "attempting to deref unknown reference ~a" r))))]
    [`(set ,e1 ,e2)
      (let ([r (interpret/core e1 Γ Σ)])
      (if (dict-has-key? Σ r) (dict-set! Σ r (interpret/core e2 Γ Σ))
        (err (format "attempting to update unknown reference ~a" r))))
      'sole]

    [`(λ (,x : ,t) ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret/core e1 Γ Σ)
        [`(λ ,x ,e1 ,env)
          (interpret/core e1 (dict-set env x (interpret/core e2 Γ Σ)) Σ)]
        [e1 (err (format "attempting to interpret arg ~a applied to unknown expression ~a" e2 e1))])]))

;; Checks an expression against some type, in a given context.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ)
  (-> stlc-ref/expr? stlc-ref/type? dict? boolean?)
  (match expr
    [`(new ,e)
      (match with
        [`(Ref ,t) (check/core e t Γ)]
        [_ #f])]
    [`(! ,e) (check/core e `(Ref ,with) Γ)]

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
  (-> stlc-ref/expr? dict? stlc-ref/type?)
  (match expr
    ['sole 'Unit]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [n #:when (natural? n) n]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]

    [`(new ,e) `(Ref ,(infer/core e Γ))]
    [`(! ,e)
      (match (infer/core e Γ)
        [`(Ref ,t) t]
        [t (err "attempting to deref term not of Ref type!")])]
    [`(set ,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(Ref ,t)
          (if (check/core e2 t Γ) 'Unit
            (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
              e1 t e2 (infer/core e2 Γ))))]
        [t (err (format "attempting to update non-reference ~a: ~a" e1 t))])]

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer/core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(,t1 → ,t2)
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]))
