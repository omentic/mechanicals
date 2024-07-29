#lang racket
(require "lib.rkt")
(require "base.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus with iso-recursive types

; Γ ⊢ e: [x ↦ μx.t] t
; ------------------------
; Γ ⊢ fold [μx.t] e: μx.t

; Γ ⊢ e: μx.t
; -----------------------------------
; Γ ⊢ unfold [μx.t] e: [x ↦ μx.t] t

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr)
  (interpret-core (strip (desugar expr)) #hash()))
(define (interpret-core expr Γ)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(fold ,e) `(fold ,(interpret-core e Γ))]
    [`(unfold ,e)
      (match (interpret-core e Γ)
        [`(fold ,e) e]
        [e `(unfold e)])]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret-core e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret-core e (dict-set env x (interpret-core e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (match expr
    [`(fold (μ ,x ,t) ,e)
      (match with
        [`(μ ,x ,t) (check-core e t (dict-set Γ x `(μ ,x ,t)))]
        [_ #f])]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t1 t) (check-core e t2 (dict-set Γ x t1)))]
        [_ #f])]

    [_ (equal? (infer-core expr Γ) with)]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define (infer-core expr Γ)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(fold (μ ,x ,t) ,e)
      (if (check-core e t (dict-set Γ x `(μ ,x ,t))) `(μ ,x ,t)
        (err (format "expected ~a to be of type ~a, got ~a"
          e t (infer e (dict-set Γ x `(μ ,x ,t))))))]
    [`(unfold (μ ,x ,t) ,e)
      (if (check-core e `(μ ,x ,t)) (replace t x `(μ ,x ,t))
        (err (format "expected ~a to be of type ~a, got ~a"
          e `(μ ,x ,t) (infer-core e Γ))))]

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer-core e (dict-set Γ x t)))]

    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (if (check-core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "attempting to infer an unknown expression ~a" e))]))

;; Replace all references to an expression with a value.
(define (replace expr key value)
  (match expr
    ; do not accidentally replace shadowed bindings
    [(or `(λ (,x : ,_) ,_) `(λ ,x ,_) `(μ ,x ,_)
      `(type ,x ,_ ,_)) #:when (equal? x key) expr]
    [`(,e ...) `(,@(map (λ (x) (replace x key value)) e))]
    [x #:when (equal? x key) value]
    [v v]))
