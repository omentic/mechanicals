#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus, with general recursion

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()])
  (interpret- (strip (desugar expr)) ctx))
(define (interpret- expr ctx)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [x #:when (dict-has-key? ctx x) (dict-ref ctx x)]

    [`(fix ,e)
      (match (interpret- e ctx)
        [`(λ ,x ,e ,env)
          ; FIXME: unsure what should be ctx and what should be env
          (interpret- e (dict-set ctx x `(fix (λ ,x ,e ,ctx))))]
        [e (err (format "applying fix to unknown expression ~a" e))])]

    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]
    [`(,body ,arg)
      (match (interpret- body ctx)
        [`(λ ,id ,body ,env)
          (interpret- body (dict-set env id (interpret- arg ctx)))]
        [e (err (format "applying arg ~a to unknown expression ~a" arg e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (check- (desugar expr) with Γ))
(define (check- expr with Γ)
  (let ([with (if (dict-has-key? Γ with) (dict-ref Γ with) with)])
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [(`(fix ,e) with)
      (check- (infer- e) `(→ ,with ,with) Γ)]

    [(`(λ ,x (: ,t) ,e) `(→ ,t1 ,t2))
      (and (equal? t t1) (check- e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(→ ,t1 ,t2)
          (and (equal? t2 t) (equal? t1 (infer- e2 Γ)))]
        [t #f])]

    [(e t) #f])))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr [Γ #hash()])
  (infer- (desugar expr) Γ))
(define (infer- expr Γ)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(fix ,e)
      (match (infer- e Γ)
        [`(→ ,t ,t) t]
        [t (err (format "fix expects a term of type t → t, got ~a" t))])]

    [`(λ ,x (: ,t) ,e)
      `(→ ,t ,(infer- e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(→ ,t1 ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "inferring an unknown expression ~a" e))]))
