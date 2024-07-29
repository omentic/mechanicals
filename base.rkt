#lang racket
(require "lib.rkt")
(provide (all-defined-out))

;; Base utility functions for working with the simply-typed lambda calculus

;; Provides a pretty-print utility for terms in the simply-typed lambda calculus
;;      (fmt Expr): String
(define (fmt expr)
  (match expr
    ['sole "⟨⟩"]
    [`(λ ,x ,e) (format "λ~a.[~a]" x (fmt e))]
    [`((λ ,x ,e1) ,e2) (format "~a = ~a; ~a" x (fmt e2) (fmt e1))]
    [`(λ (,x : ,t) ,e) (format "~a: ~a; ~a" x (fmt t) (fmt e))]
    [`((λ (,x : ,t) ,e1) ,e2) (format "~a: ~a; ~a = ~a; ~a" x (fmt t) x (fmt e2) (fmt e1))]
    [`(λ ,x ,e ,env) (format "λ~a.[~a]" x (fmt e))]
    [`(μ ,x ,t) (format "μ~a.~a" x (fmt t))]
    [`(let (,x : ,t) ,e ,in) (format "~a: ~a; ~a = ~a; ~a" x (fmt t) x (fmt e) (fmt in))]
    [`(let ,x ,e ,in) (format "~a = ~a; ~a" x (fmt e) (fmt in))]
    [`(set ,x ,e ,in) (format "~a := ~a; ~a" x (fmt e) (fmt in))]
    [`(,a → ,b) (format "(~a → ~a)" (fmt a) (fmt b))]
    [`(,a → ,k ,b) (format "(~a →~a ~a)" (fmt a) k (fmt b))]
    [`(Ref ,a) (format "Ref ~a" (fmt a))]
    [`(new ,a) (format "new ~a" (fmt a))]
    [`(! ,a) (format "!~a" (fmt a))]
    [`(,a ,b) (format "(~a ~a)" (fmt a) (fmt b))]
    [(hash-table (keys values) ...)
      (format "{~a}" (foldl (λ (k v acc) (format "~a: ~a;" (fmt k) (fmt v))) "" keys values))]
    [expr (format "~a" expr)]))

;; Removes typing annotations and similar constructs, for interpretation
(define (strip expr)
  (match expr
    [`(,e : ,_) (strip e)]
    [`(type ,_ ,_ ,e) (strip e)]
    [`(fold ,_ ,e) `(fold ,(strip e))]
    [`(unfold ,_ ,e) `(unfold ,(strip e))]
    [`(,e ...) `(,@(map strip e))]
    [e e]))

;; Define aliases from higher-level constructs to their core forms
(define (desugar expr)
  (match expr
    ['⟨⟩ 'sole]
    [`(ref ,e) (desugar `(new ,e))]
    [`(deref ,e) (desugar `(! ,e))]

    ; set-with-continuation
    [`(set ,e1 ,e2 ,in)
      (desugar `(let (_ : Unit) (set ,e1 ,e2) ,in))]

    ; many forms of let. this lets us elide many typing annotations
    [`(let (,id : (,a → ,k ,b)) (λ (,x : ,a) ,e) ,in)
      (desugar `((λ (,id : (,a → ,k ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,k ,b)) (λ ,x ,e) ,in)
      (desugar `((λ (,id : (,a → ,k ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,b)) (λ (,x : ,a) ,e) ,in)
      (desugar `((λ (,id : (,a → ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let (,id : (,a → ,b)) (λ ,x ,e) ,in)
      (desugar `((λ (,id : (,a → ,b)) ,in) (λ (,x : ,a) ,e)))]
    [`(let ,x (,e : ,t) ,in)
      (desugar `((λ (,x : ,t) ,in) (,e : ,t)))]
    [`(let ,x ,e ,in)
      (desugar `((λ ,x ,in) ,e))]
    [`(let ,x ,e)
      (desugar `(let ,x ,e sole))]

    ; letrec as let + fix
    [`(letrec (,x : ,t) ,e ,in)
      (desugar `(let (,x : ,t) (fix (λ (,x : ,t) ,e)) ,in))]

    [`(,e ...) `(,@(map desugar e))]
    [e e]))

    ; [`(list ,exprs ...)
      ; (foldr (λ (expr res) `(cons ,expr ,res)) 'nil)]
    ; [`(type ,x ,type ,in) ; fails b/c types are not inferrable
    ;   (desugar `(let (,x : Type) ,type ,in))]
