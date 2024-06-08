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
      #:when (dict-has-key? heap id)
      (interpret- (dict-ref heap id) ctx heap)]
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
    [`(deref ,id) (err (format "attempting to deref unknown reference ~a" id))]
    [expr (err (format "interpreting an unknown expression ~a" expr))]))

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
(interpret '
  (let id (: (→ Nat Nat)) (λ x x)
    (let r (: (Ref (→ Nat Nat))) (ref id)
      (let f (: (→ Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0))))))
