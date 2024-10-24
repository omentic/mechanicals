#lang racket
(require rackunit)
(require syntax/location)
(require (for-syntax syntax/location))

;; The simply-typed lambda calculus, with:
;; - sums, products, recursive types, ascryption
;; - bidirectional typechecking
;; - impredicative references built on a levels system
;; - explicit level stratification syntax
;; - automatic level collection
;; - [todo] implicit level stratification

;; Whether the system is *predicative* or *impredicative*.
;; The predicative system disallows quantification over references.
;; The impredicative system allows so by tweaking level rules.
(define impredicative? #f)

(define-syntax-rule (print msg)
  (eprintf "~a~%" msg))

(define-syntax-rule (dbg body)
  (let ([res body])
    (eprintf "[~a:~a] ~v = ~a~%"
      (syntax-source-file-name #'body)
      (syntax-line #'body)
      'body
      res)
    res))

(define-syntax-rule (err msg)
  (error 'error
    (format "[~a:~a] ~a"
      (syntax-source-file-name #'msg)
      (syntax-line #'msg)
      msg)))

(define-syntax (todo stx)
  (with-syntax ([src (syntax-source-file-name stx)] [line (syntax-line stx)])
    #'(error 'todo (format "[~a:~a] unimplemented" src line))))

(define (any? proc lst)
  (foldl (λ (x acc) (if (proc x) #t acc)) #f lst))

(define (all? proc lst)
  (foldl (λ (x acc) (if (proc x) acc #f)) #t lst))

;; Checks an expression for syntactic well-formedness.
;; This does not account for context, and so all symbols are valid exprs.
(define (stlc-full/expr? expr)
  (match expr
    ; Symbols are only valid if previously bound by `λ` or `case` (or if `'sole`).
    ; We can't check that here, however.
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [b #:when (boolean? b) #t]
    [`(,e : ,t)
      (and (stlc-full/expr? e) (stlc-full/type? t))]
    [`(type ,t1 ,t2 ,e)
      (and (stlc-full/type? t1) (stlc-full/type? t2) (stlc-full/expr? e))]
    [`(,e :: ,l)
      (and (stlc-full/expr? e) (stlc-full/level? l))]
    [`(level ,l ,e) ; note that level must only introduce new variables as levels
      (and (symbol? l) (stlc-full/expr? e))]
    [(or
      `(inc ,e)
      `(car ,e) `(cdr ,e)
      `(inl ,e) `(inr ,e)
      `(new ,e)  `(! ,e)
      `(fold ,e) `(unfold ,e))
      (stlc-full/expr? e)]
    [(or
      `(pair ,e1 ,e2)
      `(set ,e1 ,e2)
      `(,e1 ,e2))
      (and (stlc-full/expr? e1) (stlc-full/expr? e2))]
    [`(if ,c ,e1 ,e2)
      (and (stlc-full/expr? c) (stlc-full/expr? e1) (stlc-full/expr? e2))]
    [`(case ,c (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (and (symbol? x1) (symbol? x2)
        (stlc-full/expr? c) (stlc-full/expr? e1) (stlc-full/expr? e2))]
    [`(λ (,x : ,t) ,e)
      (and (symbol? x) (stlc-full/type? t) (stlc-full/expr? e))]
    [_ #f]))

;; Checks a value for syntactic well-formedness.
;; This does not account for context, and so all symbols are valid values.
;; A value is, a computation/expr/term does...
(define (stlc-full/value? expr)
  (match expr
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    [b #:when (boolean? b) #t]
    [`(ptr ,l ,a)
      (and (stlc-full/level? l) (symbol? a))]
    [(or `(inl ,v) `(inr ,v))
      (stlc-full/value? v)]
    [(or `(pair ,v1 ,v2) `(,v1 ,v2))
      (and (stlc-full/value? v1) (stlc-full/value? v2))]
    [`(λ (,x : ,t) ,e ,env)
      (and (symbol? x) (stlc-full/type? t) (stlc-full/expr? e) (dict? env))]
    [_ #f]))

;; Checks a level for syntactic well-formedness.
;; This does not account for context, and so all symbols are valid levels.
(define (stlc-full/level? level)
  (match level
    ; Symbols are only valid if previously bound (by `level`).
    ; We can't check that here, however.
    [x #:when (symbol? x) #t]
    [n #:when (natural? n) #t]
    ; Levels may be a list of symbols, or a list of symbols followed by a natural.
    [`(+ ,l ... ,n) #:when (natural? n)
      (all? (λ (s) (symbol? s)) l)]
    [`(+ ,l ...)
      (all? (λ (s) (symbol? s)) l)]
    [_ #f]))

;; Checks a type for syntactic well-formedness.
;; This does not account for context, and so all symbols are valid types.
(define (stlc-full/type? type)
  (match type
    ; Symbols are only valid if previously bound (by `type` or `μ`).
    ; We can't check that here, however.
    [x #:when (symbol? x) #t]
    [`(Ref ,t) (stlc-full/type? t)]
    [(or `(,t1 × ,t2) `(,t1 ⊕ ,t2))
      (and (stlc-full/type? t1) (stlc-full/type? t2))]
    [`(,t1 → ,l ,t2)
      (and (stlc-full/type? t1) (stlc-full/level? l) (stlc-full/type? t2))]
    [`(μ ,x ,t)
      (and (symbol? x) (stlc-full/type? t))]
    [_ #f]))

(define (stlc-full/ptr? expr)
  (match expr
    [`(ptr ,l ,a) (and (stlc-full/level? l) (symbol? a))]
    [_ #f]))

;; Creates a new multiset from a list.
(define/contract (list->multiset l)
  (-> list? dict?)
  (foldl
    (λ (x acc)
      (if (dict-has-key? acc x)
        (dict-set acc x (+ (dict-ref acc x) 1))
        (dict-set acc x 1)))
    #hash() l))

;; Creates a new list from a multiset.
(define/contract (multiset->list m)
  (-> dict? list?)
  (foldl
    (λ (x acc)
      (append acc (build-list (dict-ref m x) (λ (_) x))))
    '() (dict-keys m)))

;; Adds a symbol to a multiset.
(define/contract (multiset-add m1 s)
  (-> dict? symbol? dict?)
  (if (dict-has-key? m1 s)
    (dict-set m1 s (+ (dict-ref m1 s) 1))
    (dict-set m1 s 1)))

;; Queries two multisets for equality.
(define/contract (multiset-eq m1 m2)
  (-> dict? dict? boolean?)
  (if (equal? (length m1) (length m2)) #f
    (foldl
      (λ (x acc)
        (if (and acc (dict-has-key? m1 x))
          (equal? (dict-ref m1 x) (dict-ref m2 x))
          acc))
      #t (dict-keys m2))))

;; Unions two multisets. Shared members take the maximum count of each other.
(define/contract (multiset-union m1 m2)
  (-> dict? dict? dict?)
  (foldl
    (λ (x acc)
      (if (dict-has-key? acc x)
        (dict-set acc x (max (dict-ref acc x) (dict-ref m2 x)))
        (dict-set acc x (dict-ref m2 x))))
    m1 (dict-keys m2)))

;; Intersects two multisets. Shared members take the minimum count of each other.
(define/contract (multiset-intersect m1 m2)
  (-> dict? dict? dict?)
  (foldl
    (λ (x acc)
      (if (dict-has-key? m1 x)
        (dict-set acc x (min (dict-ref m1 x) (dict-ref m2 x)))
        acc))
    #hash() (dict-keys m2)))

;; Checks if a level is at its "base" form.
(define/contract (level-base? l)
  (-> stlc-full/level? boolean?)
  (match l
    [s #:when (symbol? s) #t]
    [n #:when (natural? n) (zero? n)]
    [`(+ ,s ... ,n) #:when (natural? n) (zero? n)] ; should be avoided
    [`(+ ,s ...) #t]))

;; Syntactic equality between levels is not trivial.
;; This helper function defines it.
(define/contract (level-eq? l1 l2)
  (-> stlc-full/level? stlc-full/level? boolean?)
  (match* (l1 l2)
    [(n1 n2) #:when (and (natural? n1) (natural? n2))
      (equal? n1 n2)]
    [(`(+ ,s1 ... ,n1) `(+ ,s2 ... ,n2)) #:when (and (natural? n1) (natural? n2))
      (and (equal? n1 n2) (level-eq? `(+ ,@s1) `(+ ,@s2)))]
    [(`(+ ,s1 ...) `(+ ,s2 ...))
      (multiset-eq (list->multiset s1) (list->multiset s2))]
    [(_ _) #f]))

;; Levels can carry natural numbers, and so we define a stratification between them.
;; Note: this returns FALSE if the levels are incomparable (i.e. (level-geq 'a 'b))
(define/contract (level-geq? l1 l2)
  (-> stlc-full/level? stlc-full/level? boolean?)
  (match* (l1 l2)
    [(s1 s2) #:when (and (symbol? s1) (symbol? s2))
      (equal? s1 s2)]
    [(n1 n2) #:when (and (natural? n1) (natural? n2))
      (>= n1 n2)]
    [(`(+ ,s1 ... ,n1) `(+ ,s2 ... ,n2)) #:when (and (natural? n1) (natural? n2))
      (and (level-eq? `(+ ,@s1) `(+ ,@s2)) (level-geq? n1 n2))]
    [(`(+ ,s1 ... ,n) `(+ ,s2 ...)) #:when (natural? n)
      (level-eq? `(+ ,@s1) `(+ ,@s2))]
    [(`(+ ,s1 ...) `(+ ,s2 ...))
      (multiset-eq (list->multiset s1)
        (multiset-intersect (list->multiset s1) (list->multiset s2)))]
    [(_ _) #f]))

;; We define a maximum of two levels.
;; This can return one of the two levels or an entirely new level.
(define/contract (level-max l1 l2)
  (-> stlc-full/level? stlc-full/level? stlc-full/level?)
  (match* (l1 l2)
    [(s1 s2) #:when (and (symbol? s1) (symbol? s2))
      (if (equal? s1 s2) s1 `(+ ,s1 ,s2))]
    [(n1 n2) #:when (and (natural? n1) (natural? n2))
      (max n1 n2)]
    [(`(+ ,s1 ... ,n1) `(+ ,s2 ... ,n2)) #:when (and (natural? n1) (natural? n2))
      (if (equal? s1 s2)
        `(+ ,@s1 ,(max n1 n2))
        (level-union `(+ ,@s1) `(+ ,@s2)))]
    [(`(+ ,s1 ... ,n) `(+ ,s2 ...)) #:when (natural? n)
      (if (level-geq? s1 s2)
        `(+ ,@s1 ,n)
        (level-union `(+ ,@s1) `(+ ,@s2)))]
    [(`(+ ,s1 ...) `(+ ,s2 ... ,n)) #:when (natural? n)
      (if (level-geq? s2 s1)
        `(+ ,@s2 ,n)
        (level-union `(+ ,@s1) `(+ ,@s2)))]
    [(`(+ ,s ... ,n1) n2) #:when (and (natural? n1) (natural? n2))
      `(+ ,s ... ,n1)]
    [(n1 `(+ ,s ... ,n2)) #:when (and (natural? n1) (natural? n2))
      `(+ ,s ... ,n2)]
    [(`(+ ,s ...) n) #:when (natural? n)
      `(+ ,@s ,n)]
    [(n `(+ ,s ...)) #:when (natural? n)
      `(+ ,@s ,n)]
    [(`(+ ,s1 ...) `(+ ,s2 ...))
      (level-union `(+ ,@s1) `(+ ,@s2))]))

;; A helper function to perform the union of levels.
(define/contract (level-union l1 l2)
  (-> level-base? level-base? level-base?)
  (match* (l1 l2)
    [(0 l) l]
    [(l 0) l]
    [(`(+ ,s1 ...) `(+ ,s2 ...))
      `(+ ,@(multiset->list (multiset-union (list->multiset s1) (list->multiset s2))))]))

;; We define addition in terms of our syntactic constructs.
(define/contract (level-add l1 l2)
  (-> stlc-full/level? stlc-full/level? stlc-full/level?)
  (match* (l1 l2)
    [(s1 s2) #:when (and (symbol? s1) (symbol? s2))
      `(+ ,s1 ,s2)]
    [(n1 n2) #:when (and (natural? n1) (natural? n2))
      (+ n1 n2)]
    [(`(+ ,s1 ... ,n1) `(+ ,s2 ... ,n2)) #:when (and (natural? n1) (natural? n2))
      (level-add (level-add `(+ ,@s1) `(+ ,@s2)) (+ n1 n2))]
    [(`(+ ,s1 ... ,n) `(+ ,s2 ...)) #:when (natural? n)
      (level-add (level-add `(+ ,@s1) `(+ ,@s2)) n)]
    [(`(+ ,s1 ...) `(+ ,s2 ... ,n)) #:when (natural? n)
      (level-add (level-add `(+ ,@s1) `(+ ,@s2)) n)]
    [(`(+ ,s ... ,n1) n2) #:when (and (natural? n1) (natural? n2))
      `(+ ,@s ,(+ n1 n2))]
    [(n1 `(+ ,s ... ,n2)) #:when (and (natural? n1) (natural? n2))
      `(+ ,@s ,(+ n1 n2))]
    [(`(+ ,s ...) n) #:when (natural? n)
      `(+ ,@s ,n)]
    [(n `(+ ,s ...)) #:when (natural? n)
      `(+ ,@s ,n)]
    [(`(+ ,s1 ...) `(+ ,s2 ...))
      `(+ ,@s1 ,@s2)]))

;; Decrements a level by 1.
;; ASSUMPTION: the level is not a base level (i.e. there is some n to dec)
(define/contract (level-dec l)
  (-> stlc-full/level? stlc-full/level?)
  (match l
    [n #:when (and (natural? n) (not (zero? n))) (- n 1)]
    [`(+ ,s ... 1) `(+ ,@s)]
    [`(+ ,s ... ,n) #:when (and (natural? n) (not (zero? n))) `(+ ,@s ,(- n 1))]
    [_ (err (format "attempting to decrement base level ~a" l))]))

;; Returns the "base" form of a level.
(define/contract (level-base l)
  (-> stlc-full/level? stlc-full/level?)
  (match l
    [s #:when (symbol? s) s]
    [n #:when (natural? n) 0]
    [`(+ ,s ... ,n) #:when (natural? n) `(+ ,@s)]
    [`(+ ,s ...) `(+ ,@s)]))

;; Returns the "offset" portion of a level.
(define/contract (level-offset l)
  (-> stlc-full/level? stlc-full/level?)
  (match l
    [s #:when (symbol? s) 0]
    [n #:when (natural? n) n]
    [`(+ ,s ... ,n) #:when (natural? n) n]
    [`(+ ,s ...) 0]))

;; Infers the level of a (well-formed) type in a context.
;; We need the context for type ascryption, and μ-types.
;; Otherwise, levels are syntactically inferred.
;; ASSUMPTION: the type is well-formed in the given context (i.e. all symbols bound).
;; This is not checked via contracts due to (presumably) massive performance overhead.
(define/contract (level-type t Γ)
  (-> stlc-full/type? dict? stlc-full/level?)
  (match t
    [(or 'Unit 'Bool 'Nat) 0]
    [s #:when (symbol? s) 0] ; HACK: μ-type variables, not in Γ
    [`(Ref ,t)
      (let ([l (level-type t Γ)])
      (if (and impredicative? (level-base? l))
        l (level-add l 1)))]
    [(or `(,t1 × ,t2) `(,t1 ⊕ ,t2))
      (level-max (level-type t1 Γ) (level-type t2 Γ))]
    [`(,t1 → ,l ,t2) ; FIXME: knob??
      (if (and (level-geq? l (level-type t1 Γ)) (level-geq? l (level-type t2 Γ))) l
        (err (format "annotated level ~a is less than inferred levels ~a and ~a!")))]
    [`(μ ,x ,t)
      (level-type t (dict-set Γ x `(μ ,x ,t)))]))

;; Infers the level of a (well-formed) expression.
(define/contract (level-expr e Γ)
  (-> stlc-full/expr? dict? stlc-full/level?)
  (match e
    ['sole 0]
    [n #:when (natural? n) 0]
    [b #:when (boolean? b) 0]
    [x #:when (dict-has-key? Γ x) ; free variables
      (level-type (type->whnf (dict-ref Γ x) Γ) Γ)]
    [s #:when (symbol? s) 0] ; local variables

    [`(,e : ,t)
      (let ([l1 (level-expr e Γ)] [l2 (level-type t Γ)])
        (if (level-geq? l1 l2) l1
          (err (format "annotated level ~a is less than inferred level ~a!" l1 l2))))]
    [`(type ,t1 ,t2 ,e)
      (level-expr e (dict-set Γ `(type ,t1) t2))]

    [`(level ,l ,e) ; NOTE: is this correct?
      (level-expr e Γ)]
    [`(,e :: ,l)
      (level-add l (level-expr e Γ))]

    [`(new ,e) ; FIXME; knob??
      (let ([l (level-expr e Γ)])
      (if (level-base? l) l (level-add l 1)))]

    [`(if ,c ,e1 ,e2)
      (level-max (level-expr c Γ)
        (level-max (level-expr e1 Γ) (level-expr e2 Γ)))]
    [`(case ,c (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (level-max (level-expr c Γ) ; support shadowing
        (level-max (level-expr e1 (dict-remove Γ x1))
          (level-expr e2 (dict-remove Γ x2))))]
    [`(λ (,x : ,_) ,e) ; support shadowing
      (level-expr e (dict-remove Γ x))]

    [(or `(! ,e)`(inc ,e)
      `(car ,e) `(cdr ,e)
      `(inl ,e) `(inr ,e)
      `(fold ,e) `(unfold ,e))
      (level-expr e Γ)]
    [(or `(set ,e1 ,e2) `(pair ,e1 ,e2) `(,e1 ,e2))
      (level-max (level-expr e1 Γ) (level-expr e2 Γ))]))

;; Whether a given type is a semantically valid type.
;; We assume any type in Γ is semantically valid.
;; Otherwise, we would infinitely recurse re: μ.
(define/contract (well-formed? t Γ)
  (-> stlc-full/type? dict? boolean?)
  (match t
    [(or 'Unit 'Bool 'Nat) #t]
    [s #:when (symbol? s) (dict-has-key? Γ `(type s))]
    [`(Ref ,t) (well-formed? t Γ)]
    [(or `(,t1 × ,t2) `(,t1 ⊕ ,t2)) (and (well-formed? t1 Γ) (well-formed? t2 Γ))]
    [`(,t1 → ,l ,t2)
      (and (dict-has-key? Γ `(level ,l))
        (well-formed? t1 Γ) (well-formed? t2 Γ))]
    [`(μ ,x ,t) ; check: this might infinitely recurse??
      (well-formed? t (dict-set Γ `(type ,x) `(μ ,x ,t)))]))

;; Whether a given type at a given level is semantically valid.
(define/contract (well-kinded? t l Γ)
  (-> stlc-full/type? stlc-full/level? dict? boolean?)
  (match t
    [(or 'Unit 'Bool 'Nat) (level-geq? l 0)]
    [s #:when (symbol? s)
      (if (dict-has-key? `(type ,s))
        (well-kinded? (dict-ref Γ `(type ,t))) #f)]
    [`(Ref ,t) ; FIXME: this is not entirely correct. hrm.
      (if (level-base? l)
        (well-kinded? t l Γ)
        (well-kinded? t (level-dec l) Γ))]
    [(or `(,t1 × ,t2) `(,t1 ⊕ ,t2))
      (and (well-kinded? t1 l Γ) (well-kinded? t1 l Γ))]
    [`(,t1 → ,k ,t2)
      (and (level-geq? l k) (well-kinded? t1 k Γ) (well-kinded? t2 k Γ))]
    [`(μ ,x ,t) ; HACK
      (well-kinded? t l (dict-set Γ `(type ,x) 'Unit))]))

;; Whether a given structure is the heap, in our model.
;; This is a quite useless function and is just here to note the model of the heap.
;; Our heap is a Dict[Level, List[Dict[Addr, Expr]]]. In other words:
;; - the heap is first stratified by algebraic levels, i.e. α, β, α+β, etc
;; - those heaps are then stratified by n: the level as a natural number.
#;
(define (stlc-full/heap? heap)
  (match heap
    [`((,level-var . (,subheap ...)) ...)
      (and (all? (λ (l) (stlc-full/level? l)) level-var)
        (all? (λ (n) (dict? n)) subheap))]
    [_ #f]))

;; Extends a list to have at least n+1 elements. Takes a default-generating procedure.
(define/contract (list-extend l n default)
  (-> list? natural? procedure? list?)
  (if (>= n (length l))
    (build-list (+ n 1)
      (λ (k)
        (if (< k (length l))
          (list-ref l k)
          (default))))
    l))

;; Models the allocation of an (unsized) memory pointer at an arbitrary heap level.
(define/contract (alloc! Σ l)
  (-> dict? stlc-full/level? stlc-full/ptr?)
  (let ([addr (gensym)] [base (level-base l)] [offset (level-offset l)])
  (if (dict-has-key? Σ base)
    (let ([base-heap (dict-ref Σ base)])
    (if (>= offset (length base-heap))
      (dict-set! Σ base ; FIXME: we probably should error if location is occupied
        (let ([offset-heap (make-hash)])
        (dict-set! offset-heap addr 'null) ; FIXME: probably should not be null
        (list-set (list-extend base-heap offset make-hash) offset offset-heap)))
      (let ([offset-heap (list-ref base-heap offset)])
      (dict-set! offset-heap addr 'null))))
    (dict-set! Σ base
      (let ([offset-heap (make-hash)])
      (dict-set! offset-heap addr 'null)
      (list-set (build-list (+ offset 1) (λ (_) (make-hash))) offset offset-heap))))
  `(ptr ,l ,addr)))

;; Updates the heap given a pointer to a memory location and a value.
(define/contract (write! Σ p v)
  (-> dict? stlc-full/ptr? stlc-full/value? stlc-full/ptr?)
  (match p
    [`(ptr ,l ,a)
      (let ([base (level-base l)] [offset (level-offset l)])
      (if (dict-has-key? Σ base)
        (let ([base-heap (dict-ref Σ base)])
        (if (< offset (length base-heap))
          (dict-set! (list-ref base-heap offset) a v)
          (err (format "writing to invalid memory location ~a!" p))))
        (err (format "writing to invalid memory location ~a!" p))))])
  p)

;; Returns the corresponding value of a pointer to a memory location on the heap.
(define/contract (read! Σ p)
  (-> dict? stlc-full/ptr? stlc-full/value?)
  (match p
    [`(ptr ,l ,a)
      (let ([base (level-base l)] [offset (level-offset l)])
      (if (dict-has-key? Σ base)
        (let ([base-heap (dict-ref Σ base)])
        (if (< offset (length base-heap))
          (dict-ref (list-ref base-heap offset) a)
          (err (format "reading from invalid memory location ~a!" p))))
        (err (format "reading from invalid memory location ~a!" p))))]))

;; Models the deallocation of all memory locations of level `l` or higher.
;; For complexity and performance purposes, we only support deallocating base levels.
(define/contract (dealloc! Σ l)
  (-> dict? level-base? void?)
  (for-each
    (λ (key)
      (if (level-geq? key l)
        (dict-remove! Σ key) (void)))
    (dict-keys Σ)))

;; Whether two types are equivalent in a context.
;; We define equivalence as equivalence up to α-renaming.
(define/contract (equiv-type t1 t2 Γ)
  (-> stlc-full/type? stlc-full/type? dict? boolean?)
  (equiv-type/core t1 t2 Γ Γ))
(define (equiv-type/core t1 t2 Γ1 Γ2)
  (match* (t1 t2)
    ; bound identifiers: if a key exists in the context, look it up
    [(x1 x2) #:when (dict-has-key? Γ1 `(type ,x1))
      (equiv-type/core (dict-ref Γ1 `(type ,x1)) x2 Γ1 Γ2)]
    [(x1 x2) #:when (dict-has-key? Γ2 `(type ,x2))
      (equiv-type/core x1 (dict-ref Γ2 `(type ,x2)) Γ1 Γ2)]

    ; recursive types: self-referential names can be arbitrary
    [(`(μ ,x1 ,t1) `(μ ,x2 ,t2))
      (let ([name gensym])
      (equiv-type/core t1 t2 (dict-set Γ1 `(type ,x1) name) (dict-set Γ2 `(type ,x2) name)))]

    ; check for syntactic equivalence on remaining forms
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv-type/core x1 x2 Γ1 Γ2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))

;; Whether two expressions are equivalent in a context.
;; We define equivalence as equivalence up to α-renaming.
; (define/contract (equiv-expr e1 e2 Γ)
;   (-> stlc-full/expr? stlc-full/expr? dict? boolean?)
;   (equiv-expr-core e1 e2 Γ Γ))
; (define (equiv-expr-core e1 e2 Γ1 Γ2)
;   (match* (e1 e2)))

;; Expands a type alias into weak-head normal form, for literal matching.
(define/contract (type->whnf t Γ)
  (-> stlc-full/type? dict? stlc-full/type?)
  (if (dict-has-key? Γ `(type ,t))
    (type->whnf (dict-ref Γ `(type ,t)) Γ) t))

;; Replaces all references to a type alias with another alias.
(define/contract (replace-type type key value)
  (-> stlc-full/type? stlc-full/type? stlc-full/type? stlc-full/type?)
  (match type
    ; Do not accidentally replace shadowed bindings
    [`(μ ,x _) #:when (equal? x key) type]
    [`(,e ...) `(,@(map (λ (x) (replace-type x key value)) e))]
    [x #:when (equal? x key) value]
    [v v]))

;; Evaluates an expression to a value.
;; Follows the call-by-value evaluation strategy.
(define (call-by-value expr)
  (cbv/core (desugar expr) #hash() (make-hash)))
(define/contract (cbv/core expr Γ Σ) ; ℓ
  (-> stlc-full/expr? dict? dict? stlc-full/value?)
  (match expr
    ['sole 'sole]
    [n #:when (natural? n) n]
    [b #:when (boolean? b) b]
    [p #:when (dict-has-key? Σ p) p]
    [x #:when (dict-has-key? Γ x) (dict-ref Γ x)]
    [f #:when (symbol? f) f]

    [`(,e : ,t)
      (cbv/core e Γ Σ)]
    [`(type ,t1 ,t2 ,e)
      (cbv/core e (dict-set Γ `(type ,t1) t2) Σ)]

    ; The (level ...) syntax introduces new level *variables*.
    [`(level ,l ,e)
      (let ([v (cbv/core e (dict-set Γ `(level ,l) 'level) Σ)])
      (dealloc! Σ l) v)] ; they are then freed at the end of scope
    [`(,e :: ,l)
      (cbv/core e Γ Σ)]

    [`(new ,e)
      (let ([p (alloc! Σ (level-expr e Γ))])
      (write! Σ p (cbv/core e Γ Σ)))]
    [`(! ,e)
      (match (cbv/core e Γ Σ)
        [`(ptr ,l ,a) (read! Σ `(ptr ,l ,a))]
        [e (err (format "attempting to deref unknown expression ~a, expected ptr" e))])]
    [`(set ,e1 ,e2) ; FIXME: we do NOT check levels before writing here
      (match (cbv/core e1 Γ Σ)
        [`(ptr ,l ,a) (write! Σ `(ptr ,l ,a) (cbv/core e2 Γ Σ))]
        [e (err (format "attempting to write to unknown expression ~a, expected ptr" e))])]

    [`(inc ,e)
      (match (cbv/core e Γ Σ)
        [n #:when (natural? n) (+ n 1)]
        [e (err (format "incrementing an unknown value ~a" e))])]
    [`(if ,c ,e1 ,e2)
      (match (cbv/core c Γ Σ)
        ['#t (cbv/core e1 Γ Σ)]
        ['#f (cbv/core e2 Γ Σ)]
        [e (err (format "calling if on unknown expression ~a" e))])]

    [`(pair ,e1 ,e2)
      `(pair ,(cbv/core e1 Γ Σ) ,(cbv/core e2 Γ Σ))]
    [`(car ,e)
      (match (cbv/core e Γ Σ)
        [`(pair ,e1 ,e2) e1]
        [e (err (format "calling car on unknown expression ~a" e))])]
    [`(cdr ,e)
      (match (cbv/core e Γ Σ)
        [`(pair ,e1 ,e2) e2]
        [e (err (format "calling cdr on unknown expression ~a" e))])]

    [`(inl ,e)
      `(inl ,(cbv/core e Γ Σ))]
    [`(inr ,e)
      `(inr ,(cbv/core e Γ Σ))]
    [`(case ,e (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (cbv/core e Γ Σ)
        [`(inl ,e) (cbv/core e1 (dict-set Γ x1 e) Σ)]
        [`(inr ,e) (cbv/core e2 (dict-set Γ x2 e) Σ)]
        [e (err (format "calling case on unknown expression ~a" e))])]

    [`(fold ,e) `(fold ,(cbv/core e Γ Σ))]
    [`(unfold ,e)
      (match (cbv/core e Γ Σ)
        [`(fold ,e) e]
        [e (err (format "attempting to unfold unknown expression ~a" e))])]

    [`(λ (,x : ,t) ,e)
      `(λ (,x : ,t) ,e ,Γ)]
    [`(,e1 ,e2)
      (match (cbv/core e1 Γ Σ)
        [`(λ (,x : ,t) ,e1 ,env)
          (cbv/core e1 (dict-set env x (cbv/core e2 Γ Σ)) Σ)]
        [e1 (err (format "attempting to interpret arg ~a applied to unknown expression ~a" e2 e1))])]))

;; Checks that an expression is of a type, and returns #t or #f, or a bubbled-up error.
;; `with` must be a type in weak-head normal form for structural matching.
(define (check expr with)
  (check/core (desugar expr) with #hash()))
(define/contract (check/core expr with Γ)
  (-> stlc-full/expr? stlc-full/type? dict? boolean?)
  (match expr
    [`(type ,t1 ,t2 ,e)
      (check/core e with (dict-set Γ `(type ,t1) t2))]

    [`(level ,l ,e) ; We add the level to the context just to note it is valid.
      (check/core e with (dict-set Γ `(level ,l) 'level))]

    [`(new ,e)
      (match with
        [`(Ref ,t) (check/core e t Γ)]
        [_ #f])]
    [`(! ,e)
      (check/core e `(Ref ,with) Γ)]

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
    ; We do not technically need case in check form.
    ; We keep it here to avoid needing type annotations on `c`.
    [`(case ,c (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer/core c Γ)
        [`(,a1 ⊕ ,a2)
          (and (check/core e1 with (dict-set Γ x1 a1))
               (check/core e2 with (dict-set Γ x2 a2)))]
        [_ #f])]

    [`(fold ,e)
      (match with
        [`(μ ,x ,t) (check/core e t (dict-set Γ `(type ,x) `(μ ,x ,t)))]
        [_ #f])]

    [`(λ (,x : ,t) ,e)
      (match with
        [`(,t1 → ,l ,t2)
          (and (equiv-type t t1 Γ) (check/core e t2 (dict-set Γ x t))
            (if impredicative?
              (> l (level-expr e (dict-set Γ x t1)))
              (>= l (level-expr e (dict-set Γ x t1)))))]
        [_ #f])]

    [_ (equiv-type (infer/core expr Γ) with Γ)]))

;; Infers a type from a given expression, if possible. Errors out otherwise.
;; Returns a type in weak-head normal form for structural matching.
(define (infer expr)
  (infer/core (desugar expr) #hash()))
;; Γ is our context: a dictionary from symbols to types??? i forget actually
;; note: our context plays many roles.
(define/contract (infer/core expr Γ)
  (-> stlc-full/expr? dict? stlc-full/type?)
  (match expr
    ['sole 'Unit]
    [n #:when (natural? n) 'Nat]
    [b #:when (boolean? b) 'Bool]
    ; We expand into weak-head normal form as the binding may be to another binding.
    [x #:when (dict-has-key? Γ x)
      (type->whnf (dict-ref Γ x) Γ)]
    [f #:when (symbol? f)
      (err (format "attempting to infer type of free variable ~a" f))]

    [`(type ,t1 ,t2 ,e)
      (infer/core e (dict-set Γ `(type ,t1) t2))]
    [`(,e : ,t)
      (if (check/core e (type->whnf t Γ) Γ) (type->whnf t Γ)
        (err (format "expression ~a is not of annotated type ~a" e t)))]

    [`(level ,l ,e) ; We add the level to the context just to note it is valid.
      (infer/core e (dict-set Γ `(level ,l) 'level))]
    [`(,e :: ,l) ; We retrieve the level from the context to check it is valid.
      (if (dict-has-key? Γ `(level ,(level-base l)))
        (infer/core e Γ)
        (err (format "level ~a not found in context, was it introduced?")))]

    [`(new ,e)
      `(Ref ,(infer/core e Γ))]
    [`(ptr ,a)
      (err (format "cannot infer type from raw pointer ~a" `(ptr ,a)))]
    [`(! ,e)
      (match (infer/core e Γ)
        [`(Ref ,t) t]
        [t (err (format "attempting to deref term ~a of type ~a" e t))])]
    [`(set ,e1 ,e2) ; FIXME: this does not account for explicit allocation syntax!
      (match (infer/core e1 Γ) ; should we check levels?
        [`(Ref ,t)
          (if (check/core e2 t Γ) 'Unit
            (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
              e1 t e2 (infer/core e2 Γ))))]
        [t (err (format "attempting to update non-reference ~a: ~a" e1 t))])]

    [`(inc ,e)
      (if (check/core e 'Nat Γ) 'Nat
        (err (format "calling inc on incorrect type ~a, expected Nat" (infer/core e Γ))))]
    [`(if ,c ,e1 ,e2)
      (if (check/core c 'Bool Γ)
        (let ([t (infer/core e1 Γ)])
        (if (check/core e2 t Γ) t
          (err (format "if ~a is not of consistent type!"
            `(if Bool ,t ,(infer/core e2 Γ))))))
        (err (format "if ~a has incorrect type ~a on condition, expected Bool"
          c (infer/core c Γ))))]

    [`(pair ,e1 ,e2)
      `(,(infer/core e1 Γ) × ,(infer/core e2 Γ))]
    [`(car ,e)
      (match (infer/core e Γ)
        [`(,t1 × ,t2) t1]
        [t (err (format "calling car on incorrect type ~a, expected a product" t))])]
    [`(cdr ,e)
      (match (infer/core e Γ)
        [`(,t1 × ,t2) t2]
        [t (err (format "calling cdr on incorrect type ~a, expected a product" t))])]

    [`(inl ,e)
      (err (format "unable to infer the type of a raw inl"))]
    [`(inr ,e)
      (err (format "unable to infer the type of a raw inr"))]
    [`(case ,c (,x1 ⇒ ,e1) (,x2 ⇒ ,e2))
      (match (infer/core c Γ)
        [`(,a1 ⊕ ,a2)
          (let ([b1 (infer/core e1 (dict-set Γ x1 a1))]
                [b2 (infer/core e2 (dict-set Γ x2 a2))])
          (if (equiv-type b1 b2 Γ) b1
            (err (format "case ~a is not of consistent type!"
              `(case (,a1 ⊕ ,a2) (,x1 ⇒ ,b1) (,x2 ⇒ ,b2))))))]
        [t (err (format "case has incorrect type ~a on condition, expected a sum" t))])]

    [`(unfold ,e)
      (match (infer/core e Γ)
        [`(μ ,x ,t) (replace-type t x `(μ ,x ,t))]
        [t (err (format "expected ~a to be of recursive type, got ~a" e t))])]

    [`(λ (,x : ,t1) ,e)
      (let* ([t2 (infer/core e (dict-set Γ x t1))]
             [t1 (type->whnf t1 Γ)]
             [l (level-expr e (dict-set Γ x t1))])
      `(,t1 → ,(if impredicative? (+ l 1) l) ,t2))]
    [`(,e1 ,e2)
      (match (infer/core e1 Γ)
        [`(,t1 → ,l ,t2) ; should we check levels here? probably redundant
          (if (check/core e2 t1 Γ) t2
            (err (format "inferred argument type ~a does not match arg ~a of type ~a"
              t1 e2 (infer/core e2 Γ))))]
        [t (err (format "expected → type on application body, got ~a" t))])]))


;; Define aliases from higher-level constructs to lower-level core forms.
(define (desugar expr)
  (match expr
    ; convenient aliases
    ['⟨⟩ 'sole]
    [`(ref ,e) (desugar `(new ,e))]
    [`(deref ,e) (desugar `(! ,e))]
    [`(,e ⇑ ,k) (desugar `(,e :: ,k))]

    ; set-with-continuation
    [`(set ,e1 ,e2 ,in)
      (desugar `(let (_ : Unit) (set ,e1 ,e2) ,in))]

    ; many forms of let. this lets us elide many typing annotations
    [`(let (,id : (,a → ,k ,b)) (λ (,x : ,a) ,e) ,in)
      (desugar `((λ (,id : (,a → ,k ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,k ,b)) (λ ,x ,e) ,in)
      (desugar `((λ (,id : (,a → ,k ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,b)) (λ (,x : ,a) ,e) ,in)
      (desugar `((λ (,id : (,a → ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,b)) (λ ,x ,e) ,in)
      (desugar `((λ (,id : (,a → ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let ,x (,e : ,t) ,in)
      (desugar `((λ (,x : ,t) ,in) (,e : ,t)))]
    [`(let ,x ,e ,in)
      (desugar `((λ ,x ,in) ,e))]
    [`(let ,x ,e)
      (desugar `(let ,x ,e sole))]

    ; desugar all remaining constructions
    [`(,e ...) `(,@(map desugar e))]
    [e e]))

;; (type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)))
(check-equal?
  (call-by-value '
    (let (next : ((μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)) → 1
                  (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))))
      (λ (self : (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)))
        (case (unfold self)
          (some ⇒ (! (cdr (cdr some))))
          (none ⇒ (fold (inr sole)))))
    (let (my_list : (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)))
      (fold
        (inl
          (pair 413
          (pair (new (inr sole))
                (new (inr sole))))))
    (next my_list))))
  '(inr sole))

(check-equal?
  (infer '
    (type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
    (λ (self : DoublyLinkedList)
       (case (unfold self)
        (some ⇒ ((! (cdr (cdr some))) : DoublyLinkedList))
        (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))))
  '((μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)) → 1 (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))))

(check-true
  (equiv-type
    (infer '
      (type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
      (λ (self : DoublyLinkedList)
         (case (unfold self)
          (some ⇒ (! (cdr (cdr some))))
          (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))))
  '(DoublyLinkedList → 1 DoublyLinkedList)
    #hash(((type DoublyLinkedList) . (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))))))

(check-true
  (check '
    (type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
    (let (get : (DoublyLinkedList → 1 (Nat ⊕ Unit)))
      (λ self
        (case (unfold self)
          (some ⇒ (inl (car some)))
          (none ⇒ (inr sole))))
    (let (prev : (DoublyLinkedList → 1 DoublyLinkedList))
      (λ self
        (case (unfold self)
          (some ⇒ (! (car (cdr some))))
          (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))
    (let (next : (DoublyLinkedList → 1 DoublyLinkedList))
      (λ self
        (case (unfold self)
          (some ⇒ (! (cdr (cdr some))))
          (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))
    (let (my_list : DoublyLinkedList)
      (fold (inl
        (pair 413
        (pair (new ((fold (inr sole)) : DoublyLinkedList))
              (new ((fold (inr sole)) : DoublyLinkedList))))))
    (prev my_list))))))
    'DoublyLinkedList))
