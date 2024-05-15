#lang racket ; note: do NOT use racket/base
(require "lib.rkt")

;; the simply-typed lambda calculus, with let sugar

(define (dict-get dict key)
  (dict-ref dict key (λ () (err (format "identifier ~a not found" key)))))

(define (value? val) (or (number? val) (string? val)))

; note: default arguments MUST all be at the end
;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()])
  (match expr
    [val #:when (value? val) val]
    [val #:when (symbol? val) (interpret (dict-get ctx val) ctx)]
    [`((λ ,id ,body) ,arg)
      (interpret body (dict-set ctx id (interpret arg ctx)))]
    [`((λ ,id (: ,type) ,body) ,arg) ; desugaring
      (interpret `((λ ,id ,body) ,expr) ctx)]
    [`(let ,id ,expr ,body)
      (interpret `((λ ,id ,body) ,expr) ctx)]
    [`(let ,id (: ,type) ,expr ,body)
      (interpret `((λ ,id ,body) ,expr) ctx)]
    [`(: ,type) ; error handling
      (err (format "interpreting a type ~a" type))]
    [`(λ ,id ,body)
      (err (format "interpreting an abstraction ~a" `(λ ,id ,body)))]
    [expr (err (format "interpreting an unknown expression ~a" expr))]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [ctx #hash()])
  (match expr
    [val #:when (or (value? val) (symbol? val))
      (equiv with (infer val ctx))]
    [`(λ ,id ,body)
      (match with
        [`(→ ,a ,b) (check body b (dict-set ctx id a))]
        [_ (err (format "expected → type to check λ with but received ~a" with))])]
    [`((λ ,id (: (→ ,a ,b)) ,body) ,arg)
      (and (check arg a ctx) (equiv with b)
        (check `(λ ,id ,body) `(→ ,a ,b) (dict-set ctx id a)))]
    [`(let ,id ,expr ,body) ; desugaring
      (check `((λ ,id ,body) ,expr) with ctx)]
    [`(let ,id (: ,type) ,expr ,body)
      (check `((λ ,id (: ,type) ,body) ,expr) with ctx)]
    [`((λ ,id ,body) (: ,type) ,arg) ; error handling
      (err (format "expected → type on λ but received ~a" type))]
    [expr (err (format "inferring an unknown expression ~a" expr))]))

;;      (equiv Type Type): Bool
(define (equiv a b)
  (match* (a b)
    [[`(ref ,a) `(ref ,b)] (equiv a b)]
    [[`(→ ,a ,c) `(→ ,b ,d)] (and (equiv a b) (equiv c d))]
    [[a b] (equal? a b)]))

;;      (infer Expr Table[Sym, Type]) → Type
(define (infer expr [ctx #hash()])
  (match expr
    [val #:when (string? val) 'Str]
    [val #:when (and (number? val) (>= val 0)) 'Nat]
    [val #:when (symbol? val) (dict-get ctx val)]
    [`((λ ,id ,body) ,arg)
      (infer body (dict-set ctx id (infer arg ctx)))]
    [`((λ ,id (: (→ ,a ,b)) ,body) ,arg)
      (if (check `((λ ,id ,body) ,arg) `(: (→ ,a ,b)) ctx)
        `(→ ,a ,b)
        (err (format "inferred type of ~a does not match annotated type ~a"
          `((λ ,id ,body) ,arg) `(: (→ ,a ,b)))))]
    [`(let ,id ,expr ,body) ; desugaring
      (infer `((λ ,id ,expr) ,body) ctx)]
    [`(let ,id (: ,type) ,expr ,body)
      (infer `((λ ,id (: ,type) ,expr) ,body) ctx)]
    [`(λ ,id ,body) ; error handling
      (err "unable to infer type from a function")]
    [`(: ,type) (err "inferring from a type annotation")]
    [expr (err (format "inferring an unknown expression ~a" expr))]))
