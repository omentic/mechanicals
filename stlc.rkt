#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()])
  (interpret- (strip expr) ctx))
(define (interpret- expr ctx)
  (match expr
    [x #:when (dict-has-key? ctx x) (dict-ref ctx x)]
    [`(λ ,x ,e) `(λ ,x ,e ,ctx)]
    [`(,e1 ,e2)
      (match (interpret- e1 ctx)
        [`(λ ,x ,e1 ,env) (interpret- e1 (dict-set env x (interpret- e2 ctx)))]
        [e1 `(,e1 ,(interpret- e2 ctx))])]
    [e e]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (match* (expr with)
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]
    [(`(λ ,x (: ,t) ,e) `(→ ,t1 ,t2))
      (and (equal? t t1) (check e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer e1 Γ)
        [`(→ ,t1 ,t2) (and (equal? t2 t) (equal? t1 (infer e2 Γ)))]
        [t (err (format "expected → type on application body, got ~a" t))])]
    [(e t) (err (format "checking an unknown expression ~a with type ~a" e t))]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr [Γ #hash()])
  (match expr
    [`(λ ,x (: ,t) ,e)
      `(→ ,t ,(infer e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer e1 Γ)
        [`(→ ,t1 ,t2)
          (if (check e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]
    [e (err (format "attempting to infer an unknown expression ~a" e))]))

(provide interpret check infer)
