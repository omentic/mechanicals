#lang racket
(require "lib.rkt")
(require "base.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus with higher-order references

;; Whether the system is *predicative* or *impredicative*.
;; The predicative system disallows quantification over references.
;; The impredicative system allows so by tweaking level rules.
(define impredicative? #f)

;; Checks an expression for syntactic well-formedness.
(define (stlc-hor/expr? expr)
  (match expr
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [(or `(new ,e) `(! ,e)) (stlc-hor/expr? e)]
    [(or `(set ,e1 ,e2) `(,e1 ,e2)) (and (stlc-hor/expr? e1) (stlc-hor/expr? e2))]
    [`(λ (,x : ,t) ,e) (and (symbol? x) (stlc-hor/type? t) (stlc-hor/expr? e))]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
(define (stlc-hor/type? type)
  (match type
    [t #:when (symbol? t) #t]
    [`(,t1 → ,k ,t2) (and (natural? k) (stlc-hor/type? t1) (stlc-hor/type? t2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc-hor/value? value)
  (match value
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [`(,v1 ,v2) (and (stlc-hor/value? v1) (stlc-hor/value? v2))]
    [`(λ ,x ,e ,env) (and (symbol? x) (stlc-hor/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define (interpret expr)
  (interpret/core (desugar expr) #hash() (make-hash)))
(define/contract (interpret/core expr Γ Σ)
  (-> stlc-hor/expr? dict? dict? stlc-hor/value?)
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

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret/core e1 Γ Σ)
        [`(λ ,x ,e1 ,env)
          (interpret/core e1 (dict-set env x (interpret/core e2 Γ Σ)) Σ)]
        [e1 (err (format "attempting to interpret arg ~a applied to unknown expression ~a" e2 e1))])]))

;; Checks an expression against some type, in a given context.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ)
  (-> stlc-hor/expr? stlc-hor/type? dict? boolean?)
  (match expr
    [`(new ,e)
      (match with
        [`(Ref ,t) (check/core e t Γ)]
        [_ #f])]
    [`(! ,e)
      (check/core e `(Ref ,with) Γ)]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,k ,t2)
          (and (equal? t t1) (check/core e t2 (dict-set Γ x t))
            (if impredicative?
              (> k (level-expr e (dict-set Γ x t1)))
              (>= k (level-expr e (dict-set Γ x t1)))))]
        [_ #f])]

    [_ (equal? (infer/core expr Γ) with)]))

;; Infers a type from some expression, in a given context.
(define (infer expr)
  (infer/core (desugar expr) #hash()))
(define/contract (infer/core expr Γ)
  (-> stlc-hor/expr? dict? stlc-hor/type?)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
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

    [`(λ (,x : ,t1) ,e)
      (let ([t2 (infer/core e (dict-set Γ x t1))]
            [k (level-expr e (dict-set Γ x t1))])
      `(,t1 → ,(if impredicative? (+ k 1) k) ,t2))]
    [`(,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(,t1 → ,k ,t2)
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a"
              t1 e2 (infer/core e2 Γ))))]
        [t (err (format "expected → type on application body, got ~a" t))])]))

;; Get the level associated with a type. This is known at compile time.
(define/contract (level-type type)
  (-> stlc-hor/type? natural?)
  (match type
    [(or 'Unit 'Nat) 0]
    [`(Ref ,t)
      (let ([k (level-type t)])
      (if (and impredicative? (zero? k)) 0 (+ 1 k)))]
    [`(,t1 → ,k ,t2)
      (if (and (>= k (level-type t1)) (>= k (level-type t2))) k
        (err (format "annotated level ~a is less than inferred levels of ~a and ~a!"
          k t1 t2)))]
    [t (err (format "attempting to infer the level of unknown type ~a" t))]))

;; Get the level of an arbitrary expression. This is not known until runtime.
(define/contract (level-expr expr Γ)
  (-> stlc-hor/expr? dict? natural?)
  (match expr
    ['sole 0]
    [n #:when (natural? n) 0]
    [x #:when (dict-has-key? Γ x) (level-type (dict-ref Γ x))]
    [(or `(new ,e) `(! ,e) `(λ (,_ : ,_) ,e)) (level-expr e Γ)]
    [(or `(set ,e1 ,e2) `(,e1 ,e2)) (max (level-expr e1 Γ) (level-expr e2 Γ))]
    [x #:when (symbol? x) 0])) ; local variables, not in Γ
