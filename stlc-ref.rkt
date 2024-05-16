#lang racket
(require "lib.rkt")

;; the simply-typed lambda calculus with references

(define (value? val)
  (or (number? val) (string? val) (equal? 'sole val) (equal? 'true val) (equal? 'false val)))

;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()] [heap #hash()]) (interpret- (strip expr) ctx heap))
(define (interpret- expr ctx heap)
  (match expr
    ; the simply-typed lambda calculus
    [val #:when (value? val) val]           ; values. strings, bools, ints, whatever
    [val #:when (symbol? val) (cond         ; identifiers.
      [(dict-has-key? ctx val) (interpret- (dict-ref ctx val) ctx heap)]
      [(dict-has-key? heap val) (interpret- (dict-ref heap val) ctx heap)]
      [else val])] ; note: we do not distinguish between bound/unbound idents
    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]    ; first class functions. returns the λ + ctx
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]

    ; references
    [`(ref ,id) `(ref ,id)]                 ; refs. pointer to immutable bound value
    [`(deref ,id)                           ; deref. accesses a stored reference from the heap
      (interpret- (dict-get heap id) ctx heap)]
    [`(set ,id ,expr ,body)                 ; set. arbitrarily updates a reference to point elsewhere
      ; note: MUST resolve the binding before applying!! !!
      (interpret- body ctx (dict-set heap id (interpret- expr ctx heap)))]

    ; function application
    [`(,body ,arg)
      (match (interpret- body ctx heap)
        [`(λ ,id ,body)
          (interpret- body (dict-set ctx id (interpret- arg ctx heap)) heap)]
        [`(λ ,id ,body ,env)
          (interpret- body (dict-set env id (interpret- arg ctx heap)) heap)]
        [expr `(,expr ,(interpret- arg ctx heap))])]

    ; desugaring and error handling
    [`(let ,id ,expr ,body) (interpret- `((λ ,id ,body) ,expr) ctx heap)]
    [expr (err (format "interpreting an unknown expression ~a" expr))]))

;; removes typing annotations.
(define (strip expr)
  (match expr
    [`(,a ,b) `(,(strip a) ,(strip b))]
    [`(λ ,id ,body) `(λ ,id ,(strip body))]
    [`(let ,id ,expr ,body) `(let ,id ,(strip expr) ,(strip body))]
    [`(λ ,id (: ,type) ,body) (strip `(λ ,id ,body))]
    [`(let ,id (: ,type) ,expr ,body) (strip `(let ,id ,expr ,body))]
    [expr expr]))

(define (dict-get dict key)
  (dict-ref dict key (λ () (err (format "identifier ~a not found" key)))))

(define (fmt expr)
  (match expr
    [`(λ ,id ,body) (format "λ~a.[~a]" id (fmt body))]
    [`((λ ,id ,body) ,arg) (format "~a = ~a; ~a" id (fmt arg) (fmt body))]
    [`(λ ,id (: ,type) ,body) (format "~a: ~a; ~a" id (fmt type) (fmt body))]
    [`((λ ,id (: ,type) ,body) ,arg) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt arg) (fmt body))]
    [`(λ ,id ,body ,ctx) (format "λ~a.[~a]" id (fmt body))]
    [`(let ,id ,expr ,body) (format "~a = ~a; ~a" id (fmt expr) (fmt body))]
    [`(let ,id (: ,type) ,expr ,body) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt expr) (fmt body))]
    [`(set ,id ,expr ,body) (format "~a := ~a; ~a" id (fmt expr) (fmt body))]
    [`(→ ,a ,b) (format "(~a → ~a)" (fmt a) (fmt b))]
    [`(Ref ,a) (format "Ref ~a" (fmt a))]
    [`(ref ,a) (format "&~a" (fmt a))]
    [`(deref ,a) (format "*~a" (fmt a))]
    [`(,a ,b) (format "(~a ~a)" (fmt a) (fmt b))]
    [(hash-table) "{}"]
    [(hash-table (k v)) (format "{~a: ~a}" (fmt k) (fmt v))]
    [(hash-table (k1 v1) (k2 v2)) (format "{~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2))]
    [(hash-table (k1 v1) (k2 v2) (k3 v3)) (format "{~a: ~a; ~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2) (fmt k3) (fmt v3))]
    [expr (format "~a" expr)]))

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
(interpret '
  (let id (: (→ Nat Nat)) (λ x x)
    (let r (: (Ref (→ Nat Nat))) (ref id)
      (let f (: (→ Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0))))))
