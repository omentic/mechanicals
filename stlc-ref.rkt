#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with references

;;      (interpret Expr Table[Sym, Expr] Table[Sym, Expr]): Value
(define (interpret expr [Γ #hash()] [Σ (make-hash)])
  (interpret- (strip (desugar expr)) Γ Σ))
(define (interpret- expr Γ Σ)
  ; (print (format "interpret: ~a" (fmt expr)))
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [r #:when (dict-has-key? Σ r) r]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(new ,e)
      (let ([r (gensym)])
      (dict-set! Σ r e) r)]
    [`(! ,e)
      (let ([r (interpret- e Γ Σ)])
      (if (dict-has-key? Σ r)
        (interpret- (dict-ref Σ r) Γ Σ)
        (err (format "attempting to deref unknown reference ~a" r))))]
    [`(set ,e1 ,e2)
      (let ([r (interpret- e1 Γ Σ)])
      (if (dict-has-key? Σ r) (dict-set! Σ r (interpret- e2 Γ Σ))
        (err (format "attempting to update unknown reference ~a" r))))
      'sole]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(λ ,x ,e ,env) `(λ ,x ,e ,env)] ; ???
    [`(,e1 ,e2)
      (match (interpret- e1 Γ Σ)
        [`(λ ,x ,e1 ,env)
          (interpret- e1 (dict-set env x (interpret- e2 Γ Σ)) Σ)]
        [e1 (err (format "attempting to interpret arg ~a applied to unknown expression ~a" e2 e1))])]

    [e (err (format "attempting to interpret unknown expression ~a" e))]))

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

    [(`(new ,e) `(Ref ,t)) (check- e t Γ)]
    [(`(! ,e) t) (check- e `(Ref ,t) Γ)]
    [(`(set ,e1 ,e2) 'Unit)
      (match (infer- e1 Γ)
        [`(Ref ,t) (check- e2 t Γ)]
        [t #f])]

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

    [`(λ (,x : ,t) ,e)
      `(,t → ,(infer- e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(,t1 → ,t2)
          (if (check- e2 t1 Γ) t2
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
