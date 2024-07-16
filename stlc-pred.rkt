#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with higher-order *predicative* references

; Γ, x: τ₁ ⊢ e: τ₂    k ≥ max-level(Γ, τ₁, τ₂)
; ---------------------------------------------
; Γ ⊢ λx:τ₁.e : τ₁ →ᵏ τ₂

; Γ ⊢ e₁: τ₁ →ᵏ τ₂    Γ ⊢ e₂: τ₁
; --------------------------------
; Γ ⊢ (e₁ e₂): τ₂

; --------------------------
; Nat::Type₀, Unit::Type₀

; τ::Typeᵢ
; -------------
; Ref τ :: Typeᵢ₊₁

; τ₁::Typeᵢ, τ₂::Typeⱼ, k ≥ max-level(τ₁, τ₂)
; -----------------------------------------
; τ₁ →ᵏ τ₂ :: Typeₖ

(require (only-in "stlc-ref.rkt" interpret))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (match expr
    ['sole (equal? 'Unit with)]
    [n #:when (natural? n) (equal? 'Nat with)]
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
        [`(,t1 → ,k ,t2)
          (and
            (equal? t t1)
            (>= k (max-level e (dict-set Γ x t1) t1 t2))  ; (KNOB)
            (check-core e t2 (dict-set Γ x t1)))])]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,k ,t2)
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

    [`(λ (,x : ,t1) ,e)
      (let ([t2 (infer-core e (dict-set Γ x t1))])
      (let ([k (max-level e (dict-set Γ x t1) t1 t2)])  ; (KNOB)
        `(,t1 → ,k ,t2)))]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,k ,t2)
          (if (check-core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a" t1 e2 (infer-core e2 Γ))))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "attempting to infer an unknown expression ~a" e))]))

;;      (max-level Table[Sym, Type] Expr Type Type): Natural
(define (max-level e Γ t1 t2)
  (max
    (level-type t1)
    (level-type t2)
    (level-body e Γ)))

;;      (level-type Type): Natural
(define (level-type t)
  (match t
    ['Unit 0]
    ['Nat 0]
    [`(,t1 → ,k ,t2)
      (if (or (< k (level-type t1)) (< k (level-type t2)))
        (err (format "annotated level ~a is less than inferred levels of ~a and ~a!"
          k t1 t2))
        k)]
    [`(Ref ,t) (+ 1 (level-type t))] ; (KNOB)
    [t (err (format "attempting to infer the level of unknown type ~a" t))]))

;;      (level-body Expr Table[Sym, Type]): Natural
(define (level-body e Γ)
  (match e
    ['sole 0]
    [n #:when (natural? n) 0]
    [x #:when (dict-has-key? Γ x)
      (level-type (dict-ref Γ x))]

    [`(new ,e) (level-body e Γ)]
    [`(! ,e) (level-body e Γ)]
    [`(set ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]

    [`(λ (,x : ,t) ,e) (level-body e (dict-set Γ x t))] ; todo: should be 0?
    [`(,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [e (err (format "attempting to infer the level of unknown expression ~a" e))]))

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
#;
(interpret '
  (let (id : (Nat → 0 Nat)) (λ x x)
    (let (r : (Ref (Nat → 0 Nat))) (new id)
      (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
        (set r f
          (f 0))))))
#;
(print (fmt '
  (let (id : (Nat → 0 Nat)) (λ x x)
    (let (r : (Ref (Nat → 0 Nat))) (new id)
      (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
        (set r f
          (f 0)))))))

(require rackunit)
(check-exn
  exn:fail?
  (λ () (infer '
    (let (id : (Nat → 0 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
        (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
          (set r f
            (f 0))))))))

(check-eq?
  (infer '
    (let (id : (Nat → 0 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
        (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
          (f 0)))))
  'Nat)

(check-eq?
  (check '
    (let (id : (Nat → 0 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
        (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
          (f 0))))
    'Nat)
  #t)
