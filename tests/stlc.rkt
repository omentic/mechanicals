#lang racket
(require (except-in rackunit check))
(require "../simple/stlc.rkt")

(check-equal? (interpret '(λ (x : Foo) x)) '(λ x x #hash()))
(check-equal? (interpret '((λ (a : Bar) a) (x y))) '(x y))
(check-equal? (interpret '((λ (a : Bat) (x y)) (λ (z : Bingus) z))) '(x y))
(check-equal? (interpret '((λ (a : Baz) (a y)) x)) '(x y))
