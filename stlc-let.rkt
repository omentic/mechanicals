#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus, with let sugar and some base types

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr)
  (interpret-core (strip (desugar expr)) #hash()))
(define (interpret-core expr Γ)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret-core e1 Γ)
        [`(λ ,x ,e1 ,env) (interpret-core e1 (dict-set env x (interpret-core e2 Γ)))]
        [e1 `(,e1 ,(interpret-core e2 Γ))])]
    [e e]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]
    [(`(λ (,x : ,t) ,e) `(,t1 → ,t2))
      (and (equal? t t1) (check-core e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2) (and (equal? t2 t) (equal? t1 (infer-core e2 Γ)))]
        [t #f])]
    [(e t) #f]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define (infer-core expr Γ)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer-core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (if (check-core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]
    [e (err (format "attempting to infer an unknown expression ~a" e))]))

(provide interpret check infer)

(require rackunit)
(check-equal? (interpret '(λ x x)) '(λ x x #hash()))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))
