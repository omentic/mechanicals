#lang racket
(require "lib.rkt")
(require (only-in "stlc-ext.rkt" equiv?))

;; The Simply-Typed Lambda Calculus with higher-order *impredicative* references,
;; plus sums products booleans ascryption etc, to implement doubly-linked lists

;;      (interpret Expr Table[Sym, Expr] Table[Sym, Expr]): Value
(define (interpret expr [Γ #hash()] [Σ (make-hash)])
  (interpret- (strip (desugar expr)) Γ Σ))
(define (interpret- expr Γ Σ)
  ; (print (format "interpret: ~a" (fmt expr)))
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [r #:when (dict-has-key? Σ r) r]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]

    [`(inc ,e)
      (match (interpret- e Γ Σ)
        [n #:when (natural? n) (+ n 1)]
        [e (format "incrementing an unknown value ~a" e)])]
    [`(if ,c ,e1 ,e2)
      (match (interpret- c Γ Σ)
        ['#t (interpret- e1 Γ Σ)]
        ['#f (interpret- e2 Γ Σ)]
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

    [`(fold ,t ,e) `(fold ,t ,(interpret- e))]
    [`(unfold ,t ,e) `(unfold ,t ,(interpret- e))]

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
  ; (print (format "check: ~a with ~a" (fmt expr) with))
  (let ([with (expand with Γ)])
  (match* (expr with)
    [('sole 'Unit) #t]
    [(n 'Nat) #:when (natural? n) #t]
    [(b 'Bool) #:when (boolean? b) #t]
    [(e `(,t1 ⊕ ,t2))
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

    [(`(pair ,e1 ,e2) `(,t1 × ,t2))
      (and (check- e1 t1 Γ) (check- e2 t2 Γ))]
    [(`(car ,e) with)
      (match (infer- e Γ)
        [`(,t1 × ,t2) (equiv? t1 with Γ Γ)]
        [t #f])]
    [(`(cdr ,e) with)
      (match (infer- e Γ)
        [`(,t1 × ,t2) (equiv? t2 with Γ Γ)]
        [t #f])]

    [(`(inl ,e) with)
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) (equiv? t1 with Γ Γ)]
        [t #f])]
    [(`(inr ,e) with)
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) (equiv? t2 with Γ Γ)]
        [t #f])]
    [(`(case ,e ,f1 ,f2) with)
      (match* ((infer- f1 Γ) (infer- f2 Γ))
        [(`(,a1 → ,t1) `(,a2 → ,t2))
          (and (check- e `(,a1 ⊕ ,a2))
            (check- f1 `(,a1 → ,with) Γ) (check- f2 `(,a2 → ,with) Γ))]
        [(t1 t2) #f])]
    [(`(,e : ,t) with)
      (and (equiv? t with Γ Γ) (check- e t Γ))]

    [(`(new ,e) `(Ref ,t)) (check- e t Γ)]
    [(`(! ,e) t) (check- e `(Ref ,t) Γ)]
    [(`(set ,e1 ,e2) 'Unit)
      (match (infer- e1 Γ)
        [`(Ref ,t) (check- e2 t Γ)]
        [t #f])]

    [(`(fold (μ ,x ,t) ,e) `(μ ,x ,t))
      (check- e t (dict-set Γ x `(μ ,x ,t)))]
    [(`(unfold (μ ,x ,t) ,e) with)
      (and (check- e `(μ ,x ,t) Γ)
        (equiv? with t #hash() #hash((x . `(μ ,x ,t)))))]

    [(`(λ (,x : ,t) ,e) `(,t1 → ,k ,t2))
      (and
        (equiv? t t1 Γ Γ)
        (> k (max-level e t1 t2 (dict-set Γ x t1)))  ; KNOB
        (check- e t2 (dict-set Γ x t1)))]
    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(,t1 → ,k ,t2)
          (and (equiv? t2 t Γ Γ)
               (equiv? t1 (infer- e2 Γ) Γ Γ))]
        [t #f])]

    [(e t) #f])))
    ;)

;;      (infer Expr Table[Sym, Type]): Type
(define (infer expr [Γ #hash()])
  (infer- (desugar expr) Γ))
(define (infer- expr Γ)
  ; (print (format "infer: ~a" (fmt expr)))
  (match expr
    ['sole 'Unit]
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
      `(,(infer- e1 Γ) × ,(infer- e2 Γ))]
    [`(car ,e)
      (match (infer- e Γ)
        [`(,t1 × ,t2) t1]
        [t (err (format "calling car on incorrect type ~a" t))])]
    [`(cdr ,e)
      (match (infer- e Γ)
        [`(,t1 × ,t2) t2]
        [t (err (format "calling cdr on incorrect type ~a" t))])]

    [`(inl ,e)
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) t1]
        [t (err (format "calling inl on incorrect type ~a" t))])]
    [`(inr ,e)
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) t2]
        [t (err (format "calling inr on incorrect type ~a" t))])]
    [`(case ,e ,f1 ,f2)
      (match* ((infer- f1 Γ) (infer- f2 Γ))
        [(`(,a1 → ,t1) `(,a2 → ,t2))
          (if (and (check- e `(,a1 ⊕ ,a2)) (equiv? t1 t2 Γ Γ)) t1
            (err (format "case ~a is not of consistent type!" `(case ,e ,f1 ,f2))))]
        [(t1 t2) (err (format "case ~a is malformed!" `(case ,e ,f1 ,f2)))])]
    [`(,e : ,t)
      (if (check- e t Γ) t
        (err (format "annotated expression ~a is not of annotated type ~a" e t)))]

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

    [`(fold (μ ,x ,t) ,e)
      (if (check- e t (dict-set Γ x `(μ ,x ,t))) `(μ ,x ,t)
        (err (format ("expected ~a to be of type ~a, got ~a"
          e t (infer e (dict-set Γ x `(μ ,x ,t)))))))]
    [`(unfold (μ ,x ,t) ,e)
      (if (check- e `(μ ,x ,t)) (α-convert t #hash((x . `(μ ,x ,t))))
        (err (format ("expected ~a to be of type ~a, got ~a"
          e `(μ ,x ,t) (infer- e Γ)))))]

    [`(λ (,x : ,t1) ,e)
      (let ([t2 (infer- e (dict-set Γ x t1))])
        (let ([k (+ 1 (max-level e t1 t2 (dict-set Γ x t1)))])  ; KNOB
          `(,t1 → ,k ,t2)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(,t1 → ,k ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a" t1 e2 (infer- e2 Γ))))]
        [t (err (format "expected → type on application body, got ~a" t))])]

    [e (err (format "attempting to infer an unknown expression ~a" e))]))

;;      (expand Type Table[Id, Expr ⊕ Type]): Type
(define (expand t Γ)
  (if (dict-has-key? Γ t) (dict-ref Γ t) t))

;;      (max-level Table[Sym, Type] Expr Type Type): Natural
(define (max-level e t1 t2 Γ)
  (max
    (level-type t1 Γ)
    (level-type t2 Γ)
    (level-body e Γ)))

;;      (level-type Type): Natural
(define (level-type t Γ)
  (match (expand t Γ)
    ['Unit 0]
    ['Nat 0]
    [`(,t1 → ,k ,t2)
      (if (or (< k (level-type t1 Γ)) (< k (level-type t2 Γ)))
        (err (format "annotated level ~a is less than inferred levels of ~a and ~a!"
          k t1 t2))
        k)]
    [`(Ref ,t)
      (let ([k (level-type t Γ)])
      (if (zero? k) 0 (+ 1 k)))] ; KNOB
    [t (err (format "attempting to infer the level of unknown type ~a" t))]))

;;      (level-body Expr Table[Sym, Type]): Natural
(define (level-body e Γ)
  (match e
    ['sole 0]
    [n #:when (natural? n) 0]
    [x #:when (dict-has-key? Γ x)
      (level-type (dict-ref Γ x) Γ)]
    [`(inc ,e) (level-body e Γ)]
    [`(new ,e) (level-body e Γ)]
    [`(new ,e) (level-body e Γ)]

    [`(pair ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [`(car ,e) (level-body e Γ)]
    [`(cdr ,e) (level-body e Γ)]
    [`(inl ,e) (level-body e Γ)]
    [`(inr ,e) (level-body e Γ)]
    [`(case ,e ,f1 ,f2) (max (level-body e Γ) (level-body f1 Γ) (level-body f2 Γ))]
    [`(fold (μ ,x ,t) ,e) (level-body e Γ)]
    [`(unfold (μ ,x ,t) ,e) (level-body e Γ)]

    [`(! ,e) (level-body e Γ)]
    [`(set ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [`(if ,c ,e1 ,e2) (max (level-body c Γ) (level-body e1 Γ) (level-body e2 Γ))]
    [`(λ (,x : ,t) ,e) (level-body e (dict-set Γ x t))] ; todo: should be 0?
    [`(,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]))

(require rackunit)
(check-exn
  exn:fail?
  (λ () (infer '
    (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
        (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
          (set r f
            (f 0))))))))

(check-eq?
  (infer '
    (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
        (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
          (f 0)))))
  'Nat)

(check-eq?
  (check '
    (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
        (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
          (f 0))))
    'Nat)
  #t)

(check-eq? (interpret '(if #t 1 0)) 1)
(check-eq? (interpret '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 2)
(check-eq? (infer '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 'Nat)
(check-true (check '(type Natural Nat ((λ (x : Natural) (inc x)) 1)) 'Nat))
