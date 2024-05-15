#lang racket ; note: do NOT use racket/base
(require "lib.rkt")

;; the simply-typed lambda calculus, with let sugar

(define (value? val) (or (number? val) (string? val)))

; note: default arguments MUST all be at the end
; no function overloading ;_;
;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr [ctx #hash()]) (interpret- (strip expr) ctx))
(define (interpret- expr ctx)
  (match expr
    [val #:when (value? val) val]
    [val #:when (symbol? val)
      (with-handlers
        ([exn:fail? (λ (exn) val)])
        (interpret- (dict-ref ctx val) ctx))]
    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]
    [`(,body ,arg)
      (match (interpret- body ctx)
        [`(λ ,id ,body) (interpret- body (dict-set ctx id (interpret- arg ctx)))]
        [`(λ ,id ,body ,env) (interpret- body (dict-set env id (interpret- arg ctx)))]
        [expr `(,(interpret- expr ctx) ,(interpret- arg ctx))])]
    ; desugaring and error handling
    [`(let ,id ,expr ,body) (interpret- `((λ ,id ,body) ,expr) ctx)]
    [expr (err (format "interpreting an unknown expression ~a" expr))]))

;; removes typing annotations. this is helpful for interpretation.
(define (strip expr)
  (match expr
    [`(,a ,b) `(,(strip a) ,(strip b))]
    [`(λ ,id ,body) `(λ ,id ,(strip body))]
    [`(let ,id ,expr ,body) `(let ,id ,(strip expr) ,(strip body))]
    [`(λ ,id (: ,type) ,body) (strip `(λ ,id ,body))]
    [`(let ,id (: ,type) ,expr ,body) (strip `(let ,id ,expr ,body))]
    [expr expr]))

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
    [`(λ ,id (: (→ ,a ,b)) ,body)
      (note "arg types are unable to be inferred")
      (if (check body b (dict-set ctx id a))
        `(→ ,a ,b)
        (err (format "inferred return type of ~a does not match annotated type ~a"
          `(λ ,id ,body) b)))]
    [`((λ ,id (: (→ ,a ,b)) ,body) ,arg)
      (if (check `((λ ,id ,body) ,arg) `(→ ,a ,b) ctx)
        b
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

(define (dict-get dict key)
  (dict-ref dict key (λ () (err (format "identifier ~a not found" key)))))

(require rackunit)
(check-equal? (interpret '(λ x x)) '(λ x x #hash()))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))

; todo: inference tests
