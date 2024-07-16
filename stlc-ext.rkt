#lang racket
(require "lib.rkt")
(require rackunit)
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus, with simple extensions
;; Unit/String/Natural/Boolean, pairs, sums, lists, ascryption

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr)
  (interpret-core (strip (desugar expr)) #hash()))
(define (interpret-core expr Γ)
  (match expr
    ['sole 'sole]
    [s #:when (string? s) s]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(inc ,e)
      (match (interpret-core e Γ)
        [n #:when (natural? n) (+ n 1)]
        [e (format "incrementing an unknown value ~a" e)])]
    [`(if ,c ,e1 ,e2)
      (match (interpret-core c Γ)
        ['#t (interpret-core e1 Γ)]
        ['#f (interpret-core e2 Γ)]
        [e (err (format "calling if on unknown expression ~a" e))])]

    [`(pair ,e1 ,e2)
      `(pair ,(interpret-core e1 Γ) ,(interpret-core e2 Γ))]
    [`(car ,e)
      (match (interpret-core e Γ)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (interpret-core e Γ)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e) `(inl ,(interpret-core e Γ))]
    [`(inr ,e) `(inr ,(interpret-core e Γ))]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (interpret-core e Γ)
        [`(inl ,e) (interpret-core e1 (dict-set Γ x1 e))]
        [`(inr ,e) (interpret-core e2 (dict-set Γ x2 e))]
        [e (err (format "calling case on unknown expression ~a" e))])]

    ['nil 'nil]
    [`(nil? ,e)
      (match (interpret-core e Γ)
        ['nil '#t]
        [`(cons ,e1 ,e2) '#f]
        [e (err (format "calling isnil on unknown expression ~a" e))])]
    [`(cons ,e1 ,e2)
     `(cons ,(interpret-core e1 Γ) ,(interpret-core e2 Γ))]
    [`(head ,e)
      (match (interpret-core e Γ)
        [`(cons ,e1 ,e2) (interpret-core e1 Γ)]
        [e (err (format "calling head on unknown expression ~a" e))])]
    [`(tail ,e)
      (match (interpret-core e Γ)
        [`(cons ,e1 ,e2) (interpret-core e2 Γ)]
        [e (err (format "calling tail on unknown expression ~a" e))])]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret-core e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret-core e (dict-set env x (interpret-core e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with)
  (check-core (desugar expr) with #hash()))
(define (check-core expr with Γ)
  (match expr
    ['sole (equal? 'Unit with)]
    [s #:when (string? s) (equal? 'Str with)]
    [n #:when (natural? n) (equal? 'Nat with)]
    [b #:when (boolean? b) (equal? 'Bool with)]

    [x #:when (dict-has-key? Γ x)
      (equiv? (dict-ref Γ x) with Γ Γ)]

    [`(type ,t1 ,t2 ,in)
      (check-core in with (dict-set Γ t1 t2))]

    [`(inc ,e)
      (and (equiv? 'Nat with)
        (check-core e 'Nat Γ))]
    [`(if ,c ,e1 ,e2)
      (and (check-core c 'Bool Γ)
        (check-core e1 with Γ) (check-core e2 with Γ))]

    [`(pair ,e1 ,e2)
      (match with
        [`(,t1 × ,t2) (and (check-core e1 t1 Γ) (check-core e2 t2 Γ))]
        [_ #f])]
    [`(car ,e)
      (match (infer-core e Γ)
        [`(,t1 × ,t2) (equiv? t1 with Γ Γ)]
        [_ #f])]
    [`(cdr ,e)
      (match (infer-core e Γ)
        [`(,t1 × ,t2) (equiv? t2 with Γ Γ)]
        [_ #f])]

    [`(inl ,e)
      (match (infer-core e Γ)
        [`(,t1 ⊕ ,t2) (equiv? t1 with Γ Γ)]
        [_ #f])]
    [`(inr ,e)
      (match (infer-core e Γ)
        [`(,t1 ⊕ ,t2) (equiv? t2 with Γ Γ)]
        [_ #f])]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer-core e Γ)
        [`(,a1 ⊕ ,a2)
          (and (check-core e1 with (dict-set Γ x1 a1))
            (check-core e2 with (dict-set Γ x2 a2)))]
        [_ #f])]
    [`(,e : ,t)
      (and (equiv? t with Γ Γ) (check-core e t Γ))]

    ['nil
      (match with
        [`(List ,t) #t]
        [_ #f])]
    [`(cons ,f1 ,f2)
      (match with
        [`(List ,t) (and (check-core f1 t Γ) (check-core f2 `(List ,t) Γ))]
        [_ #f])]
    [`(head ,e)
      (match (infer-core e)
        [`(List ,t) (equiv? t with Γ Γ)]
        [_ #f])]
    [`(tail ,e)
      (equiv? (infer-core e Γ) with Γ Γ)]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,t2)
          (and (equiv? t1 t Γ Γ) (check-core e t2 (dict-set Γ x t1)))]
        [_ #f])]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (and (equiv? t2 with Γ Γ) (equiv? t1 (infer-core e2 Γ) Γ Γ))]
        [_ #f])]

    [_ (equiv? (infer-core expr Γ) with Γ Γ)]))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr)
  (infer-core (desugar expr) #hash()))
(define (infer-core expr Γ)
  (match expr
    ['sole 'Unit]
    [s #:when (string? s) 'Str]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (expand (dict-ref Γ x) Γ)]

    [`(type ,t1 ,t2 ,in)
      (infer-core in (dict-set Γ t1 t2))]
    [`(,e : ,t)
      (if (check-core e (expand t Γ) Γ) (expand t Γ)
        (err (format "annotated expression ~a is not of annotated type ~a" e t)))]

    [`(inc ,e)
      (if (check-core e 'Nat Γ) 'Nat
        (err (format "calling inc on incorrect type ~a" (infer-core e Γ))))]
    [`(if ,c ,e1 ,e2)
      (if (check-core c 'Bool Γ)
        (let ([t (infer-core e1 Γ)])
        (if (check-core e2 t Γ) t
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
          (let ([b1 (infer-core e1 (dict-set Γ x1 (expand a1 Γ)))] [b2 (infer-core e2 (dict-set Γ x2 (expand a2 Γ)))])
            (if (equiv? b1 b2 Γ Γ) b1
              (err (format "case ~a is not of consistent type!" `(case (,a1 ⊕ ,a2) b1 b2)))))]
        [t (err (format "calling case on incorrect type ~a" t))])]

    ['nil (err (format "unable to infer type of empty list!"))]
    [`(cons ,e1 ,e2)
      (let ([t (infer-core e1 Γ)])
      (if (check-core e2 `(List ,t) Γ) `(List ,t)
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
      `(,(expand t Γ) → ,(infer-core e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer-core e1 Γ)
        [`(,t1 → ,t2)
          (if (check-core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "inferring an unknown expression ~a" e))]))

(define (expand t Γ)
  (if (dict-has-key? Γ t) (expand (dict-ref Γ t) Γ) t))

;; checks if two expressions are equivalent up to α-renaming and ascryption
(define (equiv? e1 e2 Γ1 Γ2)
  (match* (e1 e2)
    [(x1 x2) #:when (dict-has-key? Γ1 x1)
      (equiv? (dict-ref Γ1 x1) x2 Γ1 Γ2)]
    [(x1 x2) #:when (dict-has-key? Γ2 x2)
      (equiv? x1 (dict-ref Γ2 x2) Γ1 Γ2)]
    [(`(λ (,x1 : ,t1) ,e1) `(λ (,x2 : ,t2) ,e2))
      (let ([name gensym])
      (and (equiv? e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name))
        (equiv? t1 t2 Γ1 Γ2)))]
    [(`(λ ,x1 ,e1) `(λ ,x2 ,e2))
      (let ([name gensym])
      (equiv? e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name)))]
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv? x1 x2 Γ1 Γ2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))

(check-true (equiv? '(λ a a) '(λ b b) #hash() #hash()))
(check-true (equiv? '(λ a (λ b a)) '(λ b (λ a b)) #hash() #hash()))
(check-true (equiv? '(λ a (λ b (λ c (a (b c))))) '(λ c (λ a (λ b (c (a b))))) #hash() #hash()))
(check-eq? (interpret '(if #t 1 0)) 1)
(check-eq? (interpret '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 2)
(check-eq? (infer '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 'Nat)
(check-true (check '(type Natural Nat ((λ (x : Natural) (inc x)) 1)) 'Nat))
