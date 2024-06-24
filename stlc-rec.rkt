#lang racket
(require "lib.rkt")
(require (only-in "stlc-ext.rkt" equiv?))

;; The Simply-Typed Lambda Calculus with iso-recursive types

; Γ ⊢ e: [x ↦ μx.t] t
; ------------------------
; Γ ⊢ fold [μx.t] e: μx.t

; Γ ⊢ e: μx.t
; -----------------------------------
; Γ ⊢ unfold [μx.t] e: [x ↦ μx.t] t

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [Γ #hash()])
  (interpret- (strip (desugar expr)) Γ))
(define (interpret- expr Γ)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(fold ,e) `(fold ,(interpret- e Γ))]
    [`(unfold ,e)
      (match (interpret- e Γ)
        [`(fold ,e) e]
        [e `(unfold e)])]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret- e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret- e (dict-set env x (interpret- e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (check- (desugar expr) with Γ))
(define (check- expr with Γ)
  ; (print (format "check: ~a" (fmt expr)))
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [(`(fold (μ ,x ,t) ,e) `(μ ,x ,t))
      (check- e t (dict-set Γ x `(μ ,x ,t)))]
    [(`(unfold (μ ,x ,t) ,e) with)
      (and (check- e `(μ ,x ,t) Γ)
        (equiv? with t #hash() #hash((x . `(μ ,x ,t)))))]

    [(`(λ (,x : ,t) ,e) `(,t1 → ,t2))
      (and (equal? t t1) (check- e t2 (dict-set Γ x t1)))]

    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(,t1 → ,t2)
          (and (equal? t2 t) (equal? t1 (infer- e2 Γ)))]
        [t #f])]

    [(e t) #f]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr [Γ #hash()])
  (infer- (desugar expr) Γ))
(define (infer- expr Γ)
  ; (print (format "infer: ~a" (fmt expr)))
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(fold (μ ,x ,t) ,e)
      (if (check- e t (dict-set Γ x `(μ ,x ,t))) `(μ ,x ,t)
        (err (format "expected ~a to be of type ~a, got ~a"
          e t (infer e (dict-set Γ x `(μ ,x ,t))))))]
    [`(unfold (μ ,x ,t) ,e)
      (if (check- e `(μ ,x ,t)) (replace t x `(μ ,x ,t))
        (err (format "expected ~a to be of type ~a, got ~a"
          e `(μ ,x ,t) (infer- e Γ))))]

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer- e (dict-set Γ x t)))]

    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(,t1 → ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "attempting to infer an unknown expression ~a" e))]))
