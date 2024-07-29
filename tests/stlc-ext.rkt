#lang racket
(require (except-in rackunit check))
(require "../stlc-ext.rkt")

(check-true (equiv-term '(λ a a) '(λ b b) #hash()))
(check-true (equiv-term '(λ a (λ b a)) '(λ b (λ a b)) #hash()))
(check-true (equiv-term '(λ a (λ b (λ c (a (b c))))) '(λ c (λ a (λ b (c (a b))))) #hash()))
(check-eq? (interpret '(if #t 1 0)) 1)
(check-eq? (interpret '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 2)
(check-eq? (infer '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 'Nat)
(check-true (check '(type Natural Nat ((λ (x : Natural) (inc x)) 1)) 'Nat))
