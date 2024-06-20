#lang racket
(require "lib.rkt")
(require rackunit)
(provide (all-defined-out))

;; The Simply-Typed Lambda Calculus, with simple extensions
;; Unit/String/Natural/Boolean, pairs, sums, lists, ascryption

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [Γ #hash()])
  (interpret- (strip (desugar expr)) Γ))
(define (interpret- expr Γ)
  (match expr
    ['sole 'sole]
    [s #:when (string? s) s]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(inc ,e)
      (match (interpret- e Γ)
        [n #:when (natural? n) (+ n 1)]
        [e (format "incrementing an unknown value ~a" e)])]
    [`(if ,c ,e1 ,e2)
      (match (interpret- c Γ)
        ['#t (interpret- e1 Γ)]
        ['#f (interpret- e2 Γ)]
        [e (err (format "calling if on unknown expression ~a" e))])]

    [`(pair ,e1 ,e2)
      `(pair ,(interpret- e1 Γ) ,(interpret- e2 Γ))]
    [`(car ,e)
      (match (interpret- e Γ)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (interpret- e Γ)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e) `(inl ,(interpret- e Γ))]
    [`(inr ,e) `(inr ,(interpret- e Γ))]
    [`(case ,e ,f1 ,f2)
      (match (interpret- e Γ)
        [`(inl ,e) (interpret- `(,f1 ,e) Γ)]
        [`(inr ,e) (interpret- `(,f2 ,e) Γ)]
        [e (err (format "calling case on unknown expression ~a" e))])]

    ['nil 'nil]
    [`(nil? ,e)
      (match (interpret- e Γ)
        ['nil '#t]
        [`(cons ,e1 ,e2) '#f]
        [e (err (format "calling isnil on unknown expression ~a" e))])]
    [`(cons ,e1 ,e2)
     `(cons ,(interpret- e1 Γ) ,(interpret- e2 Γ))]
    [`(head ,e)
      (match (interpret- e Γ)
        [`(cons ,e1 ,e2) (interpret- e1 Γ)]
        [e (err (format "calling head on unknown expression ~a" e))])]
    [`(tail ,e)
      (match (interpret- e Γ)
        [`(cons ,e1 ,e2) (interpret- e2 Γ)]
        [e (err (format "calling tail on unknown expression ~a" e))])]

    [`(λ ,x ,e) `(λ ,x ,e ,Γ)]
    [`(,e1 ,e2)
      (match (interpret- e1 Γ)
        [`(λ ,x ,e ,env)
          (interpret- e (dict-set env x (interpret- e2 Γ)))]
        [e (err (format "applying arg ~a to unknown expression ~a" e2 e))])]

    [e (err (format "interpreting an unknown expression ~a" e))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (check- (desugar expr) with Γ))
(define (check- expr with Γ)
  (let ([with (expand with Γ)])
  (match* (expr with)
    [('sole 'Unit) #t]
    [(s 'Str) #:when (string? s) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(b 'Bool) #:when (boolean? b) #t]
    [(e `(+ ,t1 ,t2))
      (or (check- e t1 Γ) (check- e t2 Γ))]
    [(x _) #:when (dict-has-key? Γ x)
      (equiv? (dict-ref Γ x) with Γ Γ)]

    [(`(type ,t1 ,t2 ,in) with)
      (check- in with (dict-set Γ t1 t2))]

    [(`(inc ,e) 'Nat)
      (check- e 'Nat Γ)]
    [(`(if ,c ,e1 ,e2) with)
      (and (check- c 'Bool Γ)
        (check- e1 with Γ) (check e2 with Γ))]

    [(`(pair ,e1 ,e2) `(× ,t1 ,t2))
      (and (check- e1 t1 Γ) (check- e2 t2 Γ))]
    [(`(car ,e) with)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) (equiv? t1 with Γ Γ)]
        [t #f])]
    [(`(cdr ,e) with)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) (equiv? t2 with Γ Γ)]
        [t #f])]

    [(`(inl ,e) with)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) (equiv? t1 with Γ Γ)]
        [t #f])]
    [(`(inr ,e) with)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) (equiv? t2 with Γ Γ)]
        [t #f])]
    [(`(case ,e ,f1 ,f2) with)
      (match* ((infer- f1 Γ) (infer- f2 Γ))
        [(`(→ ,a1 ,t1) `(→ ,a2 ,t2))
          (and (check- e `(+ ,a1 ,a2))
            (check- f1 `(→ ,a1 ,with) Γ) (check- f2 `(→ ,a2 ,with) Γ))]
        [(t1 t2) #f])]
    [(`(,e (: ,t)) with)
      (and (equiv? t with Γ Γ) (check- e t Γ))]

    [('nil `(List ,t)) #t]
    [(`(cons ,f1 ,f2) `(List ,t))
      (and (check- f1 t Γ) (check- f2 `(List ,t) Γ))]
    [(`(head ,e) with)
      (match (infer- e)
        [`(List ,t) (equiv? t with Γ Γ)]
        [t #f])]
    [(`(tail ,e) with)
      (equiv? (infer- e Γ) with Γ Γ)]

    [(`(λ ,x (: ,t) ,e) `(→ ,t1 ,t2))
      (and (equiv? t t1 Γ Γ) (check- e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(→ ,t1 ,t2)
          (and (equiv? t2 t Γ Γ) (equiv? t1 (infer- e2 Γ) Γ Γ))]
        [t #f])]

    [(e t) #f])))

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr [Γ #hash()])
  (infer- (desugar expr) Γ))
(define (infer- expr Γ)
  (match expr
    ['sole 'Unit]
    [s #:when (string? s) 'Str]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(type ,t1 ,t2 ,in)
      (infer in (dict-set Γ t1 t2))]

    [`(inc ,e)
      (if (check- e 'Nat Γ) 'Nat
        (err (format "calling inc on incorrect type ~a" (infer- e Γ))))]
    [`(if ,c ,e1 ,e2)
      (if (check- c 'Bool Γ)
        (let ([t (infer- e1 Γ)])
        (if (check- e2 t Γ) t
          (err (format "condition has branches of differing types ~a and ~a"
            t (infer- e2 Γ)))))
        (err (format "condition ~a has incorrect type ~a" c (infer- c Γ))))]

    [`(pair ,e1 ,e2)
      `(× ,(infer- e1 Γ) ,(infer- e2 Γ))]
    [`(car ,e)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) t1]
        [t (err (format "calling car on incorrect type ~a" t))])]
    [`(cdr ,e)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) t2]
        [t (err (format "calling cdr on incorrect type ~a" t))])]

    [`(inl ,e)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) t1]
        [t (err (format "calling inl on incorrect type ~a" t))])]
    [`(inr ,e)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) t2]
        [t (err (format "calling inr on incorrect type ~a" t))])]
    [`(case ,e ,f1 ,f2)
      (match* ((infer- f1 Γ) (infer- f2 Γ))
        [(`(→ ,a1 ,t1) `(→ ,a2 ,t2))
          (if (and (check- e `(+ ,a1 ,a2)) (equiv? t1 t2 Γ Γ)) t1
            (err (format "case ~a is not of consistent type!" `(case ,e ,f1 ,f2))))]
        [(t1 t2) (err (format "case ~a is malformed!" `(case ,e ,f1 ,f2)))])]
    [`(,e (: ,t))
      (if (check- e t Γ) t
        (err (format "annotated expression ~a is not of annotated type ~a" e t)))]

    ['nil (err (format "unable to infer type of empty list!"))]
    [`(cons ,e1 ,e2)
      (let ([t (infer- e1 Γ)])
      (if (check- e2 `(List ,t) Γ) `(List ,t)
        (err (format "list ~a is not of consistent type!" `(cons ,e1 ,e2)))))]
    [`(head ,e)
      (match (infer- e Γ)
        [`(List ,t) t]
        [t (err (format "calling head on incorrect type ~a" t))])]
    [`(tail ,e)
      (match (infer- e Γ)
        [`(List ,t) `(List ,t)]
        [t (err (format "calling tail on incorrect type ~a" t))])]

    [`(λ ,x (: ,t) ,e)
      `(→ ,t ,(infer- e (dict-set Γ x t)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(→ ,t1 ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a" t1 e2)))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "inferring an unknown expression ~a" e))]))

(define (expand t Γ)
  (if (dict-has-key? Γ t) (dict-ref Γ t) t))

;; checks if two expressions are equivalent up to α-renaming and ascryption
(define (equiv? e1 e2 [Γ1 #hash()] [Γ2 #hash()])
  (match* (e1 e2)
    [(x1 x2) #:when (dict-has-key? Γ1 x1)
      (equiv? (dict-ref Γ1 x1) x2 Γ1 Γ2)]
    [(x1 x2) #:when (dict-has-key? Γ2 x2)
      (equiv? x1 (dict-ref Γ2 x2) Γ1 Γ2)]
    [(`(λ ,x1 (: _) ,e1) `(λ ,x2 (: _) ,e2)) ; todo: merge these into one
      (let ([name gensym])
      (equiv? e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name)))]
    [(`(λ ,x1 ,e1) `(λ ,x2 ,e2))
      (let ([name gensym])
      (equiv? e1 e2 (dict-set Γ1 x1 name) (dict-set Γ2 x2 name)))]
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv? x1 x2 Γ1 Γ2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))
(check-true (equiv? '(λ a a) '(λ b b)))
(check-true (equiv? '(λ a (λ b a)) '(λ b (λ a b))))
(check-true (equiv? '(λ a (λ b (λ c (a (b c))))) '(λ c (λ a (λ b (c (a b)))))))

(check-eq? (interpret '(if #t 1 0)) 1)
(check-eq? (interpret '(type Natural Nat ((λ x (: Natural) (inc x)) 1))) 2)
(check-eq? (infer '(type Natural Nat ((λ x (: Natural) (inc x)) 1))) 'Nat)
(check-true (check '(type Natural Nat ((λ x (: Natural) (inc x)) 1)) 'Nat))
