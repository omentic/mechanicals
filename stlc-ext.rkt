#lang racket
(require "lib.rkt")
(require "base.rkt")
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus, with simple extensions
;; Unit/String/Natural/Boolean, pairs, sums, lists, ascryption

;; Checks an expression for syntactic well-formedness.
(define (stlc-ext/expr? expr)
  (match expr
    [(or 'sole 'nil) #t]
    [s #:when (string? s) #t]
    [n #:when (natural? n) #t]
    [b #:when (boolean? b) #t]
    [x #:when (symbol? x) #t]

    [(or
      `(inc ,e)
      `(car ,e) `(cdr ,e)
      `(inl ,e) `(inr ,e)
      `(head ,e) `(tail ,e) `(nil? ,e))
      (stlc-ext/expr? e)]
    [(or
      `(pair ,e1 ,e2)
      `(cons ,e1 ,e2)
      `(,e1 ,e2))
      (and (stlc-ext/expr? e1) (stlc-ext/expr? e2))]

    [`(if ,c ,e1 ,e2)
      (and (stlc-ext/expr? c) (stlc-ext/expr? e1) (stlc-ext/expr? e2))]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (and (stlc-ext/expr? e) (stlc-ext/expr? e1) (stlc-ext/expr? e2)
        (symbol? x1) (symbol? x2))]
    [`(type ,t1 ,t2 ,e)
      (and (stlc-ext/type? t1) (stlc-ext/type? t2) (stlc-ext/expr? e))]
    [`(λ (,x : ,t) ,e)
      (and (symbol? x) (stlc-ext/type? t) (stlc-ext/expr? e))]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
(define (stlc-ext/type? type)
  (match type
    [t #:when (symbol? t) #t]
    [`(List ,t) (stlc-ext/type? t)]
    [(or
      `(,t1 → ,t2)
      `(,t1 × ,t2)
      `(,t1 ⊕ ,t2))
      (and (stlc-ext/type? t1) (stlc-ext/type? t2))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
(define (stlc-ext/value? value)
  (match value
    [(or 'sole 'nil) #t]
    [s #:when (string? s) #t]
    [n #:when (natural? n) #t]
    [b #:when (boolean? b) #t]
    [x #:when (symbol? x) #t]
    [(or
      `(pair ,v1 ,v2)
      `(cons ,v1 ,v2)
      `(,v1 ,v2))
      (and (stlc-ext/value? v1) (stlc-ext/value? v2))]
    [`(λ ,x ,e ,env)
      (and (symbol? x) (stlc-ext/expr? e) (dict? env))]
    [_ #f]))

;; Interprets an expression down to a value, in a given context.
(define (interpret expr)
  (interpret/core (desugar expr) #hash()))
(define/contract (interpret/core expr Γ)
  (-> stlc-ext/expr? dict? stlc-ext/value?)
  (match expr
    ['sole 'sole]
    [s #:when (string? s) s]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f) f]

    [`(,e : ,t) (interpret/core e Γ)]
    [`(type ,t1 ,t2 ,e) (interpret/core e Γ)]

    [`(inc ,e)
      (match (interpret/core e Γ)
        [n #:when (natural? n) (+ n 1)]
        [e (format "incrementing an unknown value ~a" e)])]
    [`(if ,c ,e1 ,e2)
      (match (interpret/core c Γ)
        ['#t (interpret/core e1 Γ)]
        ['#f (interpret/core e2 Γ)]
        [e (err (format "calling if on unknown expression ~a" e))])]

    [`(pair ,e1 ,e2)
      `(pair ,(interpret/core e1 Γ) ,(interpret/core e2 Γ))]
    [`(car ,e)
      (match (interpret/core e Γ)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (interpret/core e Γ)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e) `(inl ,(interpret/core e Γ))]
    [`(inr ,e) `(inr ,(interpret/core e Γ))]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (interpret/core e Γ)
        [`(inl ,e) (interpret/core e1 (dict-set Γ x1 e))]
        [`(inr ,e) (interpret/core e2 (dict-set Γ x2 e))]
        [e (err (format "calling case on unknown expression ~a" e))])]

    ['nil 'nil]
    [`(nil? ,e)
      (match (interpret/core e Γ)
        ['nil '#t]
        [`(cons ,e1 ,e2) '#f]
        [e (err (format "calling isnil on unknown expression ~a" e))])]
    [`(cons ,e1 ,e2)
     `(cons ,(interpret/core e1 Γ) ,(interpret/core e2 Γ))]
    [`(head ,e)
      (match (interpret/core e Γ)
        [`(cons ,e1 ,e2) (interpret/core e1 Γ)]
        [e (err (format "calling head on unknown expression ~a" e))])]
    [`(tail ,e)
      (match (interpret/core e Γ)
        [`(cons ,e1 ,e2) (interpret/core e2 Γ)]
        [e (err (format "calling tail on unknown expression ~a" e))])]

    [`(λ (,x : ,t) ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret/core e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret/core e (dict-set env x (interpret/core e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]))

;; Checks an expression against some type, in a given context.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ)
  (-> stlc-ext/expr? stlc-ext/type? dict? boolean?)
  (match expr
    [`(type ,t1 ,t2 ,in)
      (check/core in with (dict-set Γ t1 t2))]

    [`(if ,c ,e1 ,e2)
      (and (check/core c 'Bool Γ)
        (check/core e1 with Γ) (check/core e2 with Γ))]

    [`(pair ,e1 ,e2)
      (match with
        [`(,t1 × ,t2) (and (check/core e1 t1 Γ) (check/core e2 t2 Γ))]
        [_ #f])]

    [`(inl ,e)
      (match with
        [`(,t1 ⊕ ,t2) (check/core e t1 Γ)]
        [_ #f])]
    [`(inr ,e)
      (match with
        [`(,t1 ⊕ ,t2) (check/core e t2 Γ)]
        [_ #f])]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer-core e Γ)
        [`(,a1 ⊕ ,a2)
          (and (check/core e1 with (dict-set Γ x1 a1))
            (check/core e2 with (dict-set Γ x2 a2)))]
        [_ #f])]

    ['nil
      (match with
        [`(List ,t) #t]
        [_ #f])]
    [`(cons ,f1 ,f2)
      (match with
        [`(List ,t)
          (and (check/core f1 t Γ)
            (check/core f2 `(List ,t) Γ))]
        [_ #f])]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equiv-type t1 t Γ) (check/core e t2 (dict-set Γ x t1)))]
        [_ #f])]

    [_ (equiv-type (infer-core expr Γ) with Γ)]))

;; Infers a type from some expression, in a given context.
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define/contract (infer-core expr Γ)
  (-> stlc-ext/expr? dict? stlc-ext/type?)
  (match expr
    ['sole 'Unit]
    [s #:when (string? s) 'Str]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (type->whnf (dict-ref Γ x) Γ)]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]

    [`(type ,t1 ,t2 ,in)
      (infer-core in (dict-set Γ t1 t2))]
    [`(,e : ,t)
      (if (check/core e (type->whnf t Γ) Γ) (type->whnf t Γ)
        (err (format "annotated expression ~a is not of annotated type ~a" e t)))]

    [`(inc ,e)
      (if (check/core e 'Nat Γ) 'Nat
        (err (format "calling inc on incorrect type ~a" (infer-core e Γ))))]
    [`(if ,c ,e1 ,e2)
      (if (check/core c 'Bool Γ)
        (let ([t (infer-core e1 Γ)])
        (if (check/core e2 t Γ) t
          (err (format "condition has branches of differing types ~a and ~a"
            t (infer-core e2 Γ)))))
        (err (format "condition ~a has incorrect type ~a" c (infer-core c Γ))))]

    [`(pair ,e1 ,e2)
      `(,(infer-core e1 Γ) × ,(infer-core e2 Γ))]
    [`(car ,e)
      (match (infer-core e Γ)
        [`(,t1 × ,t2) t1]
        [t (err (format "calling car on incorrect type ~a" t))])]
    [`(cdr ,e)
      (match (infer-core e Γ)
        [`(,t1 × ,t2) t2]
        [t (err (format "calling cdr on incorrect type ~a" t))])]

    [`(inl ,e) ; annotations necessary
      (match (infer-core e Γ)
        [`(,t1 ⊕ ,t2) `(,t1 ⊕ ,t2)]
        [t (err (format "calling inl on incorrect type ~a" t))])]
    [`(inr ,e) ; annotations necessary
      (match (infer-core e Γ)
        [`(,t1 ⊕ ,t2) `(,t1 ⊕ ,t2)]
        [t (err (format "calling inr on incorrect type ~a" t))])]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer-core e Γ)
        [`(,a1 ⊕ ,a2)
          (let ([b1 (infer-core e1 (dict-set Γ x1 (type->whnf a1 Γ)))]
            [b2 (infer-core e2 (dict-set Γ x2 (type->whnf a2 Γ)))])
          (if (equiv-type b1 b2 Γ) b1
            (err (format "case ~a is not of consistent type!" `(case (,a1 ⊕ ,a2) b1 b2)))))]
        [t (err (format "calling case on incorrect type ~a" t))])]

    ['nil (err (format "unable to infer type of empty list!"))]
    [`(cons ,e1 ,e2)
      (let ([t (infer-core e1 Γ)])
      (if (check/core e2 `(List ,t) Γ) `(List ,t)
        (err (format "list ~a is not of consistent type!" `(cons ,e1 ,e2)))))]
    [`(head ,e)
      (match (infer-core e Γ)
        [`(List ,t) t]
        [t (err (format "calling head on incorrect type ~a" t))])]
    [`(tail ,e)
      (match (infer-core e Γ)
        [`(List ,t) `(List ,t)]
        [t (err (format "calling tail on incorrect type ~a" t))])]

    [`(λ (,x : ,t) ,e)
      `(,(type->whnf t Γ) → ,(infer-core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]))

;; Expands a type alias into weak-head normal form, for literal matching.
(define (type->whnf t Γ)
  (if (dict-has-key? Γ `(type ,t))
    (type->whnf (dict-ref Γ `(type ,t)) Γ) t))

;; Checks if two types are equivalent up to α-conversion in context
;;      (equiv-type Expr Expr Table[Sym Expr]): Bool
(define (equiv-type e1 e2 Γ)
  (equiv-type/core e1 e2 Γ Γ))
(define (equiv-type/core e1 e2 Γ1 Γ2)
  (match* (e1 e2)
    ; bound identifiers: if a key exists in the context, look it up
    [(x1 x2) #:when (dict-has-key? Γ1 x1)
      (equiv-type/core (dict-ref Γ1 x1) x2 Γ1 Γ2)]
    [(x1 x2) #:when (dict-has-key? Γ2 x2)
      (equiv-type/core x1 (dict-ref Γ2 x2) Γ1 Γ2)]

    ; check for syntactic equivalence on remaining forms
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv-type/core x1 x2 Γ1 Γ2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))

;; Checks if two terms are equivalent up to α-conversion in context
;;      (equiv-term Expr Expr Table[Sym Expr]): Bool
(define (equiv-term e1 e2 Γ)
  (equiv-term/core e1 e2 Γ Γ))
(define (equiv-term/core e1 e2 Γ1 Γ2)
  (match* (e1 e2)
    ; bound identifiers: if a key exists in the context, look it up
    [(x1 x2) #:when (dict-has-key? Γ1 x1)
      (equiv-term/core (dict-ref Γ1 x1) x2 Γ1 Γ2)]
    [(x1 x2) #:when (dict-has-key? Γ2 x2)
      (equiv-term/core x1 (dict-ref Γ2 x2) Γ1 Γ2)]

    ; function expressions: parameter names can be arbitrary
    [(`(λ (,x1 : ,t1) ,e1) `(λ (,x2 : ,t2) ,e2))
      (let ([name gensym])
      (and (equiv-term/core e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name))
        (equiv-term/core t1 t2 Γ1 Γ2)))]
    [(`(λ ,x1 ,e1) `(λ ,x2 ,e2))
      (let ([name gensym])
      (equiv-term/core e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name)))]

    ; check for syntactic equivalence on remaining forms
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv-term/core x1 x2 Γ1 Γ2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))
