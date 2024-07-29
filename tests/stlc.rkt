#lang racket
(require (except-in rackunit check))
(require "../stlc.rkt")

(check-equal? (interpret '(λ x x)) '(λ x x #hash()))
(check-equal? (interpret '((λ a a) (x y))) '(x y))
(check-equal? (interpret '((λ a (x y)) (λ z z))) '(x y))
(check-equal? (interpret '((λ a (a y)) x)) '(x y))
