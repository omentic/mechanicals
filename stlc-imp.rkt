#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with higher-order *impredicative* references

(require (only-in "stlc-ref.rkt" interpret))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (check- (desugar expr) with Γ))
(define (check- expr with Γ)
  ;   (check- expr (dict-ref Γ with) Γ)
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [(`(new ,e) `(Ref ,t)) (check- e t Γ)]
    [(`(! ,e) t) (check- e `(Ref ,t) Γ)]
    [(`(set ,e1 ,e2) 'Unit)
      (match (infer- e1 Γ)
        [`(Ref ,t) (check- e2 t Γ)]
        [t #f])]

    [(`(λ ,x (: ,t) ,e) `(→ ,k ,t1 ,t2))
      (and
        (equal? t t1)
        (> k (max-level e (dict-set Γ x t1) t1 t2))  ; KNOB
        (check- e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(→ ,k ,t1 ,t2)
          (and (equal? t2 t)
               (equal? t1 (infer- e2 Γ)))]
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
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(new ,e) `(Ref ,(infer- e Γ))]
    [`(! ,e)
      (match (infer- e Γ)
        [`(Ref ,t) t]
        [t (err "attempting to deref term not of Ref type!")])]
    [`(set ,e1 ,e2)
      (match (infer- e1 Γ)
        [`(Ref ,t)
          (if (check- e2 t Γ) 'Unit
            (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
              e1 t e2 (infer- e2 Γ))))]
        [t (err (format "attempting to update non-reference ~a: ~a" e1 t))])]

    [`(λ ,x (: ,t1) ,e)
      (let ([t2 (infer- e (dict-set Γ x t1))])
        (let ([k (+ 1 (max-level e (dict-set Γ x t1) t1 t2))])  ; KNOB
          `(→ ,k ,t1 ,t2)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(→ ,k ,t1 ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a" t1 e2 (infer- e2 Γ))))]
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
    [`(→ ,k ,t1 ,t2)
      (if (or (< k (level-type t1)) (< k (level-type t2)))
        (err (format "annotated level ~a is less than inferred levels of ~a and ~a!"
          k t1 t2))
        k)]
    [`(Ref ,t)
      (let ([k (level-type t)])
      (if (zero? k) 0 ((+ 1 k))))] ; KNOB
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
    [`(λ ,x (: ,t) ,e) (level-body e (dict-set Γ x t))] ; todo: should be 0?
    [`(,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]))
