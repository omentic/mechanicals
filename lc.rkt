#lang racket
(require "lib.rkt")

;; the untyped lambda calculus

(define (interpret expr [ctx #hash()])
  (match expr
    [val #:when (or (number? val) (string? val)) val]
    [val #:when (symbol? val)
      (with-handlers
        ([exn:fail? (λ (exn) val)]) ; note: unbound identifiers are supported
        (interpret (dict-ref ctx val) ctx))]
    [`(λ ,id ,body) `(λ ,id ,body)]
    [`(,body ,arg)
      (match (interpret body ctx)
        [`(λ ,id ,body) (interpret body (dict-set ctx id (interpret arg ctx)))]
        [expr `(,(interpret expr ctx) ,(interpret arg ctx))])]
    [expr (err (format "unknown expression ~a" expr))]))

(require rackunit)
(check-equal? (interpret '(λ x x)) '(λ x x))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))
