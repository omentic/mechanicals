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

;; normalizes an expression into binding variables descending
;;      (α-convert Expr Table[Old New] Set[New])
(define (α-convert expr [ctx '()] [used '()])
  (match expr
    [`(λ ,id ,body)
      (let ([new (fresh used)])
        `(λ ,new ,(α-convert body (dict-set ctx id new) (set-add used new))))]
    [`(,body ,arg)
      `(,(α-convert body ctx used) ,(α-convert arg ctx used))]
    [id #:when (dict-has-key? ctx id)
      (dict-ref ctx id)]
    [val #:when (symbol? val) val]
    [_ (err (format "α-converting unknown expression ~a" expr))]))

;; FIXME lmfao
(define (fresh used)
  (cond
    [(set-member? used 'i) 'j]
    [(set-member? used 'h) 'i]
    [(set-member? used 'g) 'h]
    [(set-member? used 'f) 'g]
    [(set-member? used 'e) 'f]
    [(set-member? used 'd) 'e]
    [(set-member? used 'c) 'd]
    [(set-member? used 'b) 'c]
    [(set-member? used 'a) 'b]
    [else 'a]))

(check-equal?
  (α-convert '(λ a (λ b (λ c (a (b c))))))
  (α-convert '(λ c (λ a (λ b (c (a b)))))))

; fixme: at least two issues:
; β-reduction is not normally strongly normalizing!
;  we want to find a tradeoff in presentation to get termination here
; the β-reduction step, i'm pretty sure, needs to α-convert some stuff...
;  b/c we're getting weird failures in the very last terms
;  i.e. '(λ a (λ b ((a b) a))) vs '(λ a (λ b (a a)))

;;      (β-reduce Expr Table[])
(define (β-reduce expr [ctx '()])
  (match expr
    [`(λ ,id ,body)
      `(λ ,id ,(β-reduce body ctx))]
    [`((λ ,id ,body) ,arg)
      (β-reduce body (dict-set ctx id arg))]
    [`(,id ,arg) #:when (dict-has-key? ctx id)
      (β-reduce `(,(β-reduce (dict-ref ctx id) ctx) ,arg))]
    [`(,body ,arg) `(,body ,(β-reduce arg ctx))]
    [`(,body ,arg)
      (let ([reduced (β-reduce body ctx)])
        (if (equal? body reduced)
          `(,reduced ,(β-reduce arg ctx))
          (β-reduce `(,reduced ,arg) ctx)))]
    [id #:when (dict-has-key? ctx id)
      (β-reduce (dict-ref ctx id) ctx)]
    [val #:when (symbol? val) val]
    [_ (err (format "β-reducing unknown expression ~a" expr))]))

(define (normalize expr)
  (α-convert (β-reduce expr)))

(check-equal?
  (normalize '(λ a (λ b (λ c (a (b c))))))
  (normalize '(λ c (λ a (λ b (c (a b)))))))

(provide interpret normalize α-convert β-reduce)
