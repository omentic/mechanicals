#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus, with let sugar

(define (value? val) (or (number? val) (string? val) (symbol? val)))

; note: no function overloading ;_;
;;      (interpret Expr Table[Sym, Expr]): Value
(define (interpret expr) (interpret- (strip expr) '()))
(define (interpret- expr ctx)
  (match expr
    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]
    [`(λ ,id ,body ,env) `(λ ,id ,body ,env)]
    [`((λ ,id ,body) ,arg)
      (interpret- body (dict-set ctx id (interpret- arg ctx)))]
    [`((λ ,id ,body ,env) ,arg)
      (interpret- body (dict-set env id (interpret- arg ctx)))]
    [`(,id ,arg) #:when (dict-has-key? ctx id)
      (interpret- `(,(interpret- (dict-ref ctx id) ctx) ,arg) ctx)]
    [`(,body ,arg) ; todo: how to recognize an irreducible term? this is kinda cheating, i think
      (let ([reduced (interpret- body ctx)])
        (if (equal? body reduced)
          `(,reduced ,(interpret- arg ctx))
          (interpret- `(,reduced ,arg) ctx)))]
    [id #:when (dict-has-key? ctx id)
      (interpret- (dict-ref ctx id) ctx)]
    [val #:when (value? val) val]
    [`(let ,id ,expr ,body) (interpret- `((λ ,id ,body) ,expr) ctx)]
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
    [`((λ ,id ,body) ,arg)
      (note "unable to check arg type from λ lacking annotation")
      (check body with ctx)] ; hmm
    [`(λ ,id (: ,type) ,body)
      (and (check `(λ ,id ,body) type ctx) (equiv with type))]
    [`((λ ,id (: (→ ,a ,b)) ,body) ,arg)
      (and (check arg a ctx) (equiv with b)
        (check `(λ ,id ,body) `(→ ,a ,b) (dict-set ctx id a)))]
    ; desugaring and error handling
    [`(let ,id ,expr ,body)
      (check `((λ ,id ,body) ,expr) with ctx)]
    [`(let ,id (: ,type) ,expr ,body)
      (check `((λ ,id (: ,type) ,body) ,expr) with ctx)]
    [`(λ ,id (: ,type) ,body)
      (err (format "expected → type on λ but received ~a" type))]
    [`((λ ,id (: ,type) ,body) ,arg)
      (err (format "expected → type on λ but received ~a" type))]
    [expr (err (format "inferring an unknown expression ~a" expr))]))

;;      (equiv Type Type): Bool
(define (equiv a b)
  (match* (a b)
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
      (note "unable to infer arg type from λ lacking annotation")
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
      (err "unable to infer type from λ lacking annotation")] ; hmm
    [`(λ ,id (: ,type) ,body)
      (err (format "expected → type on λ but received ~a" type))]
    [`((λ ,id (: ,type) ,body) ,arg)
      (err (format "expected → type on λ but received ~a" type))]
    [expr (err (format "inferring an unknown expression ~a" expr))]))

(define (dict-get dict key)
  (dict-ref dict key (λ () (err (format "identifier ~a not found" key)))))

(require rackunit)
(check-equal? (interpret '(λ x x)) '(λ x x #hash()))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))

; todo: inference tests
