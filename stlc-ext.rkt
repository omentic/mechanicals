#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus, with simple extensions
;; Unit/String/Natural/Boolean, pairs, sums, lists, ascryption

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()])
  (interpret- (strip (desugar expr)) ctx))
(define (interpret- expr ctx heap)
  (match expr
    ['sole 'sole]
    [s #:when (string? s) s]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [x #:when (dict-has-key? ctx x) (dict-ref ctx x)]

    [`(pair ,e1 ,e2)
      `(pair ,(interpret- e1 ctx) ,(interpret- e2 ctx))]
    [`(car ,e)
      (match (interpret- e ctx)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (interpret- e ctx)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e) `(inl ,(interpret- e ctx))]
    [`(inr ,e) `(inr ,(interpret- e ctx))]
    [`(case ,e ,f1 ,f2)
      (match (interpret- e ctx)
        [`(inl ,e) (interpret- `(,f1 ,e) ctx)]
        [`(inr ,e) (interpret- `(,f2 ,e) ctx)]
        [e (err (format "calling case on unknown expression ~a" e))])]

    ['nil 'nil]
    [`(nil? ,e)
      (match (interpret- e ctx)
        ['nil '#t]
        [`(cons ,e1 ,e2) '#f]
        [e (err (format "calling isnil on unknown expression ~a" e))])]
    [`(cons ,e1 ,e2)
     `(cons ,(interpret- e1 ctx) ,(interpret- e2 ctx))]
    [`(head ,e)
      (match (interpret- e ctx)
        [`(cons ,e1 ,e2) (interpret- e1 ctx)]
        [e (err (format "calling head on unknown expression ~a" e))])]
    [`(tail ,e)
      (match (interpret- e ctx)
        [`(cons ,e1 ,e2) (interpret- e2 ctx)]
        [e (err (format "calling tail on unknown expression ~a" e))])]

    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]
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
  ; (print (format "check: ~a" (fmt expr)))
  (let ([with (if (dict-has-key? Γ with) (dict-ref Γ with) with)])
  (match* (expr with)
    [('sole 'Unit) #t]
    [(s 'Str) #:when (string? s) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(b 'Bool) #:when (boolean? b) #t]
    [(e `(+ ,t1 ,t2))
      (or (check- e t1 Γ) (check- e t2 Γ))]
    [(x _) #:when (dict-has-key? Γ x)
      (equal? (dict-ref Γ x) with)]

    [(`(type ,t1 ,t2 ,in) with)
      (check- in with (dict-set Γ t1 t2))]

    [(`(pair ,e1 ,e2) `(× ,t1 ,t2))
      (and (check- e1 t1 Γ) (check- e2 t2 Γ))]
    [(`(car ,e) with)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) (equal? t1 with)]
        [t #f])]
    [(`(cdr ,e) with)
      (match (infer- e Γ)
        [`(× ,t1 ,t2) (equal? t2 with)]
        [t #f])]

    [(`(inl ,e) with)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) (equal? t1 with)]
        [t #f])]
    [(`(inr ,e) with)
      (match (infer- e Γ)
        [`(+ ,t1 ,t2) (equal? t2 with)]
        [t #f])]
    [(`(case ,e ,f1 ,f2) with)
      (match* ((infer- f1 Γ) (infer- f2 Γ))
        [(`(→ ,a1 ,t1) `(→ ,a2 ,t2))
          (and (check- e `(+ ,a1 ,a2))
            (check- f1 `(→ ,a1 ,with) Γ) (check- f2 `(→ ,a2 ,with) Γ))]
        [(t1 t2) #f])]
    [(`(,e (: ,t)) with)
      (and (equal? t with) (check- e t Γ))]

    [('nil `(List ,t)) #t]
    [(`(cons ,f1 ,f2) `(List ,t))
      (and (check- f1 t Γ) (check- f2 `(List ,t) Γ))]
    [(`(head ,e) with)
      (match (infer- e)
        [`(List ,t) (equal? t with)]
        [t #f])]
    [(`(tail ,e) with)
      (equal? (infer- e Γ) with)]

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
    [s #:when (string? s) 'Str]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    [x #:when (dict-has-key? Γ x)
      (dict-ref Γ x)]

    [`(type ,t1 ,t2 ,in)
      (infer in (dict-set Γ t1 t2))]

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
          (if (and (check- e `(+ ,a1 ,a2)) (equal? t1 t2)) t1
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