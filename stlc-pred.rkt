#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with higher-order *predicative* references

; add sequencing, annotate stuff properly

;; definition of values
(define (value? val)
  (or (natural? val) (equal? 'sole val)))

;;      (interpret Expr Table[Sym, Expr]) → Value
(define (interpret expr [ctx '()] [heap '()]) (interpret- (strip expr) ctx heap))
(define (interpret- expr ctx heap)
  (match expr
    [`(λ ,id ,body) `(λ ,id ,body ,ctx)] ; first class functions
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]

    [`((λ ,id ,body) ,arg) ; function application
      (interpret- body (dict-set ctx id (interpret- arg ctx heap)) heap)]
    [`((λ ,id ,body ,env) ,arg) ; uses the closure env if it exists
      (interpret- body (dict-set env id (interpret- arg ctx heap)) heap)]

    [`(ref ,id) `(ref ,id)] ; references
    [`(deref ,id) #:when (dict-has-key? heap id)
      (interpret- (dict-ref heap id) ctx heap)]
    [`(set ,id ,expr ,body) ; note: MUST resolve the binding before applying!! !!
      (interpret- body ctx (dict-set heap id (interpret- expr ctx heap)))]

    ; todo: how to recognize an irreducible term? this is kinda cheating, i think
    [`(,body ,arg) ; general application (resolves to function application or returns as an object)
      (let ([reduced (interpret- body ctx heap)])
        (if (equal? body reduced) `(,reduced ,(interpret- arg ctx heap))
          (interpret- `(,reduced ,arg) ctx heap)))] ; change! recur

    [id #:when (dict-has-key? ctx id) ; bound variables and references
      (interpret- (dict-ref ctx id) ctx heap)]
    [id #:when (dict-has-key? heap id) id]
    [val #:when (value? val) val]

    [`(let ,id ,expr ,body) ; desugaring and error handling
      (interpret- `((λ ,id ,body) ,expr) ctx heap)]
    [`(deref ,id) (err (format "attempting to deref unknown reference ~a" id))]
    [expr (err (format "interpreting an unknown expression ~a" expr))]))

;; removes typing annotations.
(define (strip expr)
  (match expr
    [`(,a ,b) `(,(strip a) ,(strip b))]
    [`(λ ,id ,body) `(λ ,id ,(strip body))]
    [`(let ,id ,expr ,body) `(let ,id ,(strip expr) ,(strip body))]
    [`(set ,id ,expr ,body) `(set ,id ,(strip expr) ,(strip body))]
    [`(λ ,id (: ,type) ,body) (strip `(λ ,id ,body))]
    [`(let ,id (: ,type) ,expr ,body) (strip `(let ,id ,expr ,body))]
    [expr expr]))

; note: this bidirectional system is incapable of inferring types of arguments from *usage*:
; i.e. in function definitions etc. i think this might only be possible with unification.
; we make note of when such cases are relevant but continue with the typechecking.

; todo: checking levels??

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  ; (print (format "check: ~a" (fmt expr)))
  (match* (expr with)
    [('sole 'Unit) #t] ; values
    [(num 'Nat) #:when (natural? num) #t]
    [(val _) #:when (dict-has-key? Γ val) (equiv? (dict-ref Γ val) with)]

    [(`(ref ,id) `(Ref ,type)) (check id type Γ)] ; references
    [(`(deref ,id) _) (check id `(Ref ,with) Γ)]
    [(`(set ,id ,expr ,body) _)
      (and (check expr (infer id Γ) Γ) (check body with Γ))]

    [(`(λ ,id ,body) `(→ ,k ,a ,b)) ; function literals
      ; note: we are unable to check argument type (a). it is totally generic
      ; (note (format "assuming annotated type ~a for argument ~a" a id))
      (and ; check level (k) and return type (b)
        (>= k (max (level a) (level b)))
        (check body b (dict-set Γ id a)))]
    [(`(λ ,id (: ,type) ,body) _)
      (and (equiv? type with) (check `(λ ,id ,body) type Γ))]

    [(`((λ ,id ,body) ,arg) _) ; function application
      (check body with (dict-set Γ id (infer arg Γ)))]
    [(`((λ ,id (: (→ ,k ,a ,b)) ,body) ,arg) _)
      (and (equiv? b with) (check arg a Γ)
        (check `(λ ,id ,body) `(→ ,k ,a ,b) (dict-set Γ id a)))]

    [(`(let ,id (: ,type) ,expr ,body) _) ; annotated parameter
      (and (check expr type Γ) (check body with (dict-set Γ id type)))]
    [(`(let ,id ,expr ,body) _) ; desugaring
      (check `((λ ,id ,body) ,expr) with Γ)]

    [(`(,body ,arg) _) ; general application
      (match (infer body Γ) ; FIXME: this is broken and i don't know why
        [`(→ ,k ,a ,b)     ; smth wrong being passed in? thinks f is of a large type when not
          (and (equiv? b with) (equiv? a (infer arg Γ)))]
        [type (err (format "expected → type on application body, got ~a" type))])]

    [(`(λ ,id (: ,type) ,body) _) ; error handling
      (err (format "expected → type on λ but received ~a" type))]
    [(`((λ ,id (: ,type) ,body) ,arg) _)
      (err (format "expected → type on λ but received ~a" type))]
    [(`(λ ,id ,body) `(→ ,a ,b))
      (err "you forgot to add a level annotation dummy")]
    [(expr _) (err (format "inferring an unknown expression ~a" expr))]))

;;      (infer Expr Table[Sym, Type]) → Type
(define (infer expr [Γ #hash()])
  ; (print (format "infer: ~a" (fmt expr)))
  (match expr
    ['sole 'Unit] ; values
    [val #:when (natural? val) 'Nat]
    [val #:when (dict-has-key? Γ val) (dict-ref Γ val)]

    [`(ref ,id) `(Ref ,(infer id Γ))] ; references
    [`(deref ,id)
      (match (infer id Γ)
        [`(Ref ,type) type]
        [_ (err "attempting to deref term not of Ref type!")])]
    [`(set ,id ,expr ,body) #:when (dict-has-key? Γ id)
      (if (check expr
        (match (dict-ref Γ id) ; all ref types in Γ are of form (Ref ,type):
          [`(Ref ,type) type]  ; so we must deconstruct them to continue typechecking.
          [_ (err "attempting to call set on term not of Ref type!")]) Γ)
        (infer body Γ)
        (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
          id (dict-ref Γ id) expr (infer expr Γ))))]

    [`(λ ,id ,body) ; function abstraction
      (err "unable to infer type from λ lacking annotation")] ; hmm. can we fix this?
    [`(λ ,id (: (→ ,k ,a ,b)) ,body) ; return annotation after checking it is correct
      (if (check `(λ ,id ,body) `(→ ,k ,a ,b) Γ) `(→ ,k ,a ,b)
        (err (format "inferred return type of ~a does not match annotated type ~a"
          `(λ ,id ,body) b)))]

    [`((λ ,id ,body) ,arg) ; function application
      (infer body (dict-set Γ id (infer arg Γ)))]
    [`((λ ,id (: (→ ,k ,a ,b)) ,body) ,arg) ; check arg and body separately
      (if (and (check arg a Γ) (check `(λ ,id ,body) `(→ ,k ,a ,b) Γ)) b
        (err (format "inferred type of ~a does not match annotated type ~a"
          `((λ ,id ,body) ,arg) `(: (→ ,k ,a ,b)))))]

    [`(,body ,arg) ; general application
      (match (infer body Γ)
        [`(→ ,k ,a ,b)
          (if (check arg a Γ) b
            (err (format "inferred argument type ~a does not match arg ~a" a arg)))]
        [`(→ ,a ,b) (err "you forgot to add a level annotation dummy")]
        [type (err (format "expected → type on application body, got ~a" type))])]

    [`(let ,id (: ,type) ,expr ,body) ; annotated parameter
      (if (check expr type Γ) (infer body (dict-set Γ id type))
        (err (format "inferred argument type ~a does not match arg ~a" type expr)))]

    [`(let ,id ,expr ,body) ; desugaring
      (infer `((λ ,id ,expr) ,body) Γ)]

    [`(λ ,id (: ,type) ,body) ; error handling
      (err (format "expected → type on λ but received ~a" type))]
    [`((λ ,id (: ,type) ,body) ,arg)
      (err (format "expected → type on λ but received ~a" type))]
    [`(set ,id ,expr ,body)
      (err (format "attempting to update unknown reference ~a" id))]
    [expr (err (format "inferring an unknown expression ~a" expr))]))

; todo: when checking, disregard levels on the individual types??? hmmmmmmm
;;      (equiv? Type Type) → Bool
(define (equiv? a b)
  (match* (a b)
    ; [[`(→ ,j ,a ,c) `(→ ,k ,b ,d)] (and (equiv? a b) (equiv? c d))]
    [[a b] (equal? a b)]))

;;      (level Type) → Natural
(define (level type)
  (match type
    ['Unit 0]
    ['Nat 0]
    [`(→ ,k ,a ,b) k]
    [`(Ref ,t) (+ 1 (level t))]
    [type (err (format "inferring the level of unknown type ~a" type))]))

;;      (fmt Expr) → String
(define (fmt expr)
  (match expr
    ['sole "⟨⟩"]
    [`(λ ,id ,body) (format "λ~a.[~a]" id (fmt body))]
    [`((λ ,id ,body) ,arg) (format "~a = ~a; ~a" id (fmt arg) (fmt body))]
    [`(λ ,id (: ,type) ,body) (format "~a: ~a; ~a" id (fmt type) (fmt body))]
    [`((λ ,id (: ,type) ,body) ,arg) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt arg) (fmt body))]
    [`(λ ,id ,body ,env) (format "λ~a.[~a]" id (fmt body))]
    [`(let ,id ,expr ,body) (format "~a = ~a; ~a" id (fmt expr) (fmt body))]
    [`(let ,id (: ,type) ,expr ,body) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt expr) (fmt body))]
    [`(set ,id ,expr ,body) (format "~a := ~a; ~a" id (fmt expr) (fmt body))]
    [`(→ ,a ,b) (format "(~a → ~a)" (fmt a) (fmt b))]
    [`(→ ,k ,a ,b) (format "(~a →~a ~a)" (fmt a) k (fmt b))]
    [`(Ref ,a) (format "Ref ~a" (fmt a))]
    [`(ref ,a) (format "new ~a" (fmt a))]
    [`(deref ,a) (format "!~a" (fmt a))]
    [`(,a ,b) (format "(~a ~a)" (fmt a) (fmt b))]
    [(hash-table) "{}"] ; fixme lmao
    [(hash-table (k v)) (format "{~a: ~a}" (fmt k) (fmt v))]
    [(hash-table (k1 v1) (k2 v2)) (format "{~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2))]
    [(hash-table (k1 v1) (k2 v2) (k3 v3)) (format "{~a: ~a; ~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2) (fmt k3) (fmt v3))]
    [expr (format "~a" expr)]))

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
#;
(interpret '
  (let id (: (→ 0 Nat Nat)) (λ x x)
    (let r (: (Ref (→ 0 Nat Nat))) (ref id)
      (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0))))))
#;
(print (fmt '
  (let id (: (→ 0 Nat Nat)) (λ x x)
    (let r (: (Ref (→ 0 Nat Nat))) (ref id)
      (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0)))))))

(require rackunit)
(check-exn
  exn:fail?
  (λ () (infer '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (set r f
            (f 0))))))))

(check-eq?
  (infer '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (f 0)))))
  'Nat)

(check-eq?
  (check '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (f 0))))
    'Nat)
  #t)
