#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with references

;;      (interpret Expr Table[Sym, Expr] Table[Sym, Expr]): Value
(define (interpret expr)
  (interpret-core (strip (desugar expr)) #hash() (make-hash)))
(define (interpret-core expr Γ Σ)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [r #:when (dict-has-key? Σ r) r]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(new ,e)
      (let ([r (gensym)])
      (dict-set! Σ r e) r)]
    [`(! ,e)
      (let ([r (interpret-core e Γ Σ)])
      (if (dict-has-key? Σ r)
        (interpret-core (dict-ref Σ r) Γ Σ)
        (err (format "attempting to deref unknown reference ~a" r))))]
    [`(set ,e1 ,e2)
      (let ([r (interpret-core e1 Γ Σ)])
      (if (dict-has-key? Σ r) (dict-set! Σ r (interpret-core e2 Γ Σ))
        (err (format "attempting to update unknown reference ~a" r))))
      'sole]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(λ ,x ,e ,env) `(λ ,x ,e ,env)] ; ???
    [`(,e1 ,e2)
      (match (interpret-core e1 Γ Σ)
        [`(λ ,x ,e1 ,env)
          (interpret-core e1 (dict-set env x (interpret-core e2 Γ Σ)) Σ)]
        [e1 (err (format "attempting to interpret arg ~a applied to unknown expression ~a" e2 e1))])]

    [e (err (format "attempting to interpret unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (match expr
    ['sole
      (equal? 'Unit with)]
    [n #:when (natural? n)
      (equal? 'Nat with)]
    [x #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [`(new ,e)
      (match with
        [`(Ref ,t) (check-core e t Γ)]
        [_ #f])]
    [`(! ,e) (check-core e `(Ref ,with) Γ)]
    [`(set ,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(Ref ,t)
          (and (equal? 'Unit with)
            (check-core e2 t Γ))]
        [_ #f])]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equal? t1 t) (check-core e t2 (dict-set Γ x t1)))]
        [_ #f])]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (and (equal? t2 with) (equal? t1 (infer-core e2 Γ)))]
        [_ #f])]

    [_ #f]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define (infer-core expr Γ)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(new ,e) `(Ref ,(infer-core e Γ))]
    [`(! ,e)
      (match (infer-core e Γ)
        [`(Ref ,t) t]
        [t (err "attempting to deref term not of Ref type!")])]
    [`(set ,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(Ref ,t)
          (if (check-core e2 t Γ) 'Unit
            (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
              e1 t e2 (infer-core e2 Γ))))]
        [t (err (format "attempting to update non-reference ~a: ~a" e1 t))])]

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

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
#;
(interpret '
  (let (id : (Nat → Nat)) (λ x x)
    (let (r : (Ref (Nat → Nat))) (new id)
      (let (f : (Nat → Nat)) (λ x ((! r) x))
        (set r f
          (f 0))))))
