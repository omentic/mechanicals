#lang racket
(require "lib.rkt")
(require (only-in "stlc-ext.rkt" equiv?))
(require rackunit)

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
      `(pair ,(interpret- e1 Γ Σ) ,(interpret- e2 Γ Σ))]
    [`(car ,e)
      (match (interpret- e Γ Σ)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (interpret- e Γ Σ)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e) `(inl ,(interpret- e Γ Σ))]
    [`(inr ,e) `(inr ,(interpret- e Γ Σ))]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (interpret- e Γ Σ)
        [`(inl ,e) (interpret- e1 (dict-set Γ x1 e) Σ)]
        [`(inr ,e) (interpret- e2 (dict-set Γ x2 e) Σ)]
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

    [`(fold ,e) `(fold ,(interpret- e Γ Σ))]
    [`(unfold ,e)
      (match (interpret- e Γ Σ)
        [`(fold ,e) e]
        [e `(unfold e)])]

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
      (or (equiv? (infer- e Γ) with) (check- e t1 Γ) (check- e t2 Γ))]
    [(x _) #:when (dict-has-key? Γ x)
      (equiv? (expand (dict-ref Γ x) Γ) with Γ Γ)]

    [(`(type ,t1 ,t2 ,in) with)
      (check- in with (dict-set Γ t1 (expand t2 Γ)))]

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
    [(`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2)) with)
      (equiv? with (infer- `(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2)) Γ) Γ Γ)]
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

    [(`(fold ,e) `(μ ,x ,t))
      (check- e t (dict-set Γ x `(μ ,x ,t)))]
    [(`(unfold ,e) with) ; FIXME: GROSS
      (match* ((infer- e Γ) with)
        [(`(μ ,_ ,t) `(μ ,_ ,t)) #T]
        [(t u) #f])]

    [(`(λ (,x : ,t) ,e) `(,t1 → ,k ,t2))
      (and
        (equiv? t t1 Γ Γ)
        (> k (max-level e t1 t2 (dict-set Γ x (expand t1 Γ))))  ; KNOB
        (check- e t2 (dict-set Γ x (expand t1 Γ))))]
    [(`(,e1 ,e2) t)
      (match (infer- e1 Γ)
        [`(,t1 → ,k ,t2)
          (and (equiv? t2 t Γ Γ)
               (equiv? t1 (infer- e2 Γ) Γ Γ))]
        [t #f])]

    [(e t) #f])))

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
      (infer in (dict-set Γ t1 (expand t2 Γ)))]

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

    [`(inl ,e) ; annotations necessary
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) `(,t1 ⊕ ,t2)]
        [t (err (format "calling inl on incorrect type ~a" t))])]
    [`(inr ,e) ; annotations necessary
      (match (infer- e Γ)
        [`(,t1 ⊕ ,t2) `(,t1 ⊕ ,t2)]
        [t (err (format "calling inr on incorrect type ~a" t))])]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer- e Γ)
        [`(,a1 ⊕ ,a2)
          (let ([b1 (infer- e1 (dict-set Γ x1 (expand a1 Γ)))] [b2 (infer- e2 (dict-set Γ x2 (expand a2 Γ)))])
            (if (equiv? b1 b2 Γ Γ) b1
              (err (format "case ~a is not of consistent type!" `(case (,a1 ⊕ ,a2) b1 b2)))))]
        [t (err (format "calling case on incorrect type ~a" t))])]
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
        (err (format "expected ~a to be of type ~a, got ~a"
          e t (infer e (dict-set Γ x `(μ ,x ,t))))))]
    [`(unfold (μ ,x ,t) ,e)
      (if (check- e `(μ ,x ,t)) (replace t x `(μ ,x ,t))
        (err (format "expected ~a to be of type ~a, got ~a"
          e `(μ ,x ,t) (infer- e Γ))))]

    [`(fold ,e)
      (match (infer- e Γ)
        [`(μ ,x ,t) `(μ ,x ,t)]
        [t (err (format "expected ~a to be recursive, got ~a" e t))])]
    [`(unfold ,e)
      (match (infer- e Γ)
        [`(μ ,x ,t) (replace t x `(μ ,x ,t))]
        [t (err (format "expected ~a to be recursive, got ~a" e t))])]

    [`(λ (,x : ,t1) ,e)
      (let ([t2 (infer- e (dict-set Γ x (expand t1 Γ)))])
        (let ([k (+ 1 (max-level e t1 t2 (dict-set Γ x (expand t1 Γ))))])  ; KNOB
          `(,t1 → ,k ,t2)))]
    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(,t1 → ,k ,t2)
          (if (check- e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a" t1 e2 (infer- e2 Γ))))]
        [`(,t1 → ,t2) (err (format "missing level annotation on function type"))]
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
    [`(,t1 × ,t2) (max (level-type t1 Γ) (level-type t2 Γ))]
    [`(,t1 ⊕ ,t2) (max (level-type t1 Γ) (level-type t2 Γ))]
    [`(μ ,x ,t) (level-type t (dict-set Γ x 'Unit))] ; VERY WEIRD
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
(define (level-body e Γ) ; FIXME: this part is mostly wrong
  (match e
    [`(,e : ,t) (level-type t Γ)] ; hrm
    ['sole 0]
    [n #:when (natural? n) 0]
    [x #:when (dict-has-key? Γ x)
      (level-type (dict-ref Γ x) Γ)]
    [`(inc ,e) (level-body e Γ)]
    [`(new ,e) (level-body e Γ)]

    [`(pair ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [`(car ,e) (level-body e Γ)]
    [`(cdr ,e) (level-body e Γ)]
    [`(inl ,e) (level-body e Γ)]
    [`(inr ,e) (level-body e Γ)]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (max (level-body e Γ)
           (level-body e1 (dict-set Γ x1 'Unit)) ; FIXME: totally incorrect
           (level-body e2 (dict-set Γ x2 'Unit)))]
    [`(fold (μ ,x ,t) ,e) (level-body e Γ)]
    [`(unfold (μ ,x ,t) ,e) (level-body e Γ)]
    [`(fold ,e) (level-body e Γ)]
    [`(unfold ,e) (level-body e Γ)]

    [`(! ,e) (level-body e Γ)]
    [`(set ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [`(if ,c ,e1 ,e2) (max (level-body c Γ) (level-body e1 Γ) (level-body e2 Γ))]
    [`(λ (,x : ,t) ,e) (level-body e (dict-set Γ x (expand t Γ)))] ; todo: should be 0?
    [`(,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]))


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

(check-equal?
  (infer
    '(case (inr (sole : (Nat ⊕ Unit)))
      (x ⇒ 0) (x ⇒ 1))) 'Nat)

(check-true
  (check
    '(case (inr (sole : (Nat ⊕ Unit)))
      (x ⇒ x)
      (x ⇒ 1)) 'Nat))

(check-equal?
  (interpret
    '((λ (p1 : DoublyLinkedList) (car (unfold p1)))
      (fold
        (pair 413
        (pair (inl (sole : (Unit ⊕ DoublyLinkedList)))
              (inl (sole : (Unit ⊕ DoublyLinkedList))))))))
  413)

(check-equal?
  (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
   (let get
    (λ x (car (unfold x)))
   (let my_list
    (fold
      (pair 413
      (pair (inl sole)
            (inl sole))))
   (get my_list)))))
  413)


(check-equal?
  (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
   (let prev
    (λ x
      (case (car (cdr (unfold x)))
        (x ⇒ (inl (! x)))
        (x ⇒ (inr sole))))
   (let my_list
    (fold
      (pair 413
      (pair (inl (new sole))
            (inl (new sole)))))
   (prev my_list)))))
  '(inl sole))


(check-equal?
  (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
   (let next
    (λ x
      (case (cdr (cdr (unfold x)))
        (x ⇒ (inl (! x)))
        (x ⇒ (inr sole))))
   (let my_list
    (fold
      (pair 413
      (pair (inr (new sole))
            (inr (new sole)))))
   (next my_list)))))
  '(inr sole))

(check-true
  (check
    '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
      sole)
  '(DoublyLinkedList ⊕ Unit)))

(check-equal?
  (infer '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
    (λ (p3 : DoublyLinkedList) (case (cdr (cdr (unfold p3))) (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit)))) (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit))))))))
  '(DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))

(check-true
  (check
    '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
      (λ (p3 : DoublyLinkedList) (case (cdr (cdr (unfold p3))) (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit)))) (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit)))))))
    '(DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit))))

(check-equal?
  (infer '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
    (let (get : (DoublyLinkedList → 1 Nat))
      (λ (p1 : DoublyLinkedList) (car (unfold p1)))
    (let (prev : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
      (λ (p2 : DoublyLinkedList)
        (case (car (cdr (unfold p2)))
          (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit))))
          (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit))))))
    (let (next : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
      (λ (p3 : DoublyLinkedList)
        (case (cdr (cdr (unfold p3)))
          (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit))))
          (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit))))))
    (let (my_list : DoublyLinkedList)
      (fold
        (pair 413
        (pair (inr (sole : ((Ref DoublyLinkedList) ⊕ Unit)))
              (inr (sole : ((Ref DoublyLinkedList) ⊕ Unit))))))
    (prev my_list)))))))
  '(DoublyLinkedList ⊕ Unit))

(check-true
  (check '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
    (let (get : (DoublyLinkedList → 1 Nat))
      (λ (p1 : DoublyLinkedList) (car (unfold p1)))
    (let (prev : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
      (λ (p2 : DoublyLinkedList)
        (case (car (cdr (unfold p2)))
          (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit))))
          (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit))))))
    (let (next : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
      (λ (p3 : DoublyLinkedList)
        (case (cdr (cdr (unfold p3)))
          (x ⇒ (inl ((! x) : (DoublyLinkedList ⊕ Unit))))
          (x ⇒ (inr (sole : (DoublyLinkedList ⊕ Unit))))))
    (let (my_list : DoublyLinkedList)
      (fold
        (pair 413
        (pair (inr (sole : ((Ref DoublyLinkedList) ⊕ Unit)))
              (inr (sole : ((Ref DoublyLinkedList) ⊕ Unit))))))
    (prev my_list))))))
    '(DoublyLinkedList ⊕ Unit)))
