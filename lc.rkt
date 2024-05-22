#lang racket ; note: do NOT use racket/base
(require "lib.rkt")

;; The Untyped Lambda Calculus

; note: default arguments MUST all be at the end
(define (interpret expr [ctx '()])
  (match expr
    [`(λ ,id ,body)
      `(λ ,id ,(interpret body ctx))]
    [`((λ ,id ,body) ,arg)
      (interpret body (dict-set ctx id arg))]
    [`(,id ,arg) #:when (dict-has-key? ctx id)
      (interpret `(,(interpret (dict-ref ctx id) ctx) ,arg))]
    [`(,body ,arg)
      (let ([reduced (interpret body ctx)])
        (if (equal? body reduced)
          `(,reduced ,(interpret arg ctx))
          (interpret `(,reduced ,arg) ctx)))]
    [id #:when (dict-has-key? ctx id)
      (interpret (dict-ref ctx id) ctx)]
    [val #:when (symbol? val) val]
    [_ (err (format "unknown expression ~a" expr))]))

(require rackunit)
(check-equal? (interpret '(λ x x)) '(λ x x))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))
