#lang racket
(require "lib.rkt")
(require "base.rkt")
(provide interpret check infer)

;; The Simply-Typed Lambda Calculus

;;      (interpret Expr Context): Value
(define (interpret expr [Γ #hash()])
  (match (strip expr)
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret e1 Γ)
        [`(λ ,x ,e ,env) (interpret e (dict-set env x (interpret e2 Γ)))]
        [e `(,e ,(interpret e2 Γ))])]
    [e e]))

;;      (check Expr Type Context): Bool
(define (check expr with [Γ #hash()])
  (match expr
    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t t1) (check e t2 (dict-set Γ x t)))]
        [_ #f])]
    [_ (equal? with (infer with Γ))]))

;;      (infer Expr Context): Type
(define (infer expr [Γ #hash()])
  (match expr
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer e1 Γ)
        [`(,t1 → ,t2)
          (if (check e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]
    [e (err (format "attempting to infer an unknown expression ~a" e))]))
