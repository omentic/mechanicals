#lang racket
(require syntax/location)
(require (for-syntax syntax/location))

(define-syntax-rule (dbg body)
  (let ([res body])
    (eprintf "[~a:~a] ~v = ~a~%"
      (syntax-source-file-name #'body)
      (syntax-line #'body)
      'body
      res)
    res))

(define-syntax-rule (err msg)
  (error 'error
    (format "[~a:~a] ~a"
      (syntax-source-file-name #'msg)
      (syntax-line #'msg)
      msg)))

(define-syntax-rule (note msg)
  (eprintf "note: ~a~%" msg))

(define-syntax-rule (print msg)
  (eprintf "~a~%" msg))

(define-syntax (todo stx)
  (with-syntax ([src (syntax-source-file-name stx)] [line (syntax-line stx)])
    #'(error 'todo (format "[~a:~a] unimplemented" src line))))

; todo: write a trace macro
; todo: write a fmt alias to format
; todo: write a namer

;; removes typing annotations
(define (strip expr)
  (match expr
    [`(λ ,x (: ,t) ,e (: ,t)) `(λ ,(strip x) ,(strip e))]
    [`(λ ,x ,e (: ,t)) `(λ ,(strip x) ,(strip e))]
    [`(λ ,x (: ,t) ,e) `(λ ,(strip x) ,(strip e))]
    [`(type ,t1 ,t2 ,in) (strip in)]
    [`(,e (: ,t)) (strip e)]
    [`(,e1 ,e2) `(,(strip e1) ,(strip e2))]
    [e e]))

;;      (fmt Expr) → String
(define (fmt expr)
  (match expr
    ['sole "⟨⟩"]
    [`(λ ,id ,body) (format "λ~a.[~a]" id (fmt body))]
    [`((λ ,id ,body) ,arg) (format "~a = ~a; ~a" id (fmt arg) (fmt body))]
    [`(λ ,id (: ,type) ,body) (format "~a: ~a; ~a" id (fmt type) (fmt body))]
    [`((λ ,id (: ,type) ,body) ,arg) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt arg) (fmt body))]
    [`(λ ,id ,body ,env) (format "λ~a.[~a]" id (fmt body))]
    [`(let ,id ,expr ,body) (format "~a = ~a; ~a" id (fmt expr) (fmt body))]
    [`(let ,id (: ,type) ,expr ,body) (format "~a: ~a; ~a = ~a; ~a" id (fmt type) id (fmt expr) (fmt body))]
    [`(set ,id ,expr ,body) (format "~a := ~a; ~a" id (fmt expr) (fmt body))]
    [`(→ ,a ,b) (format "(~a → ~a)" (fmt a) (fmt b))]
    [`(→ ,k ,a ,b) (format "(~a →~a ~a)" (fmt a) k (fmt b))]
    [`(Ref ,a) (format "Ref ~a" (fmt a))]
    [`(new ,a) (format "new ~a" (fmt a))]
    [`(! ,a) (format "!~a" (fmt a))]
    [`(,a ,b) (format "(~a ~a)" (fmt a) (fmt b))]
    [(hash-table) "{}"] ; fixme lmao
    [(hash-table (k v)) (format "{~a: ~a}" (fmt k) (fmt v))]
    [(hash-table (k1 v1) (k2 v2)) (format "{~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2))]
    [(hash-table (k1 v1) (k2 v2) (k3 v3)) (format "{~a: ~a; ~a: ~a; ~a: ~a}" (fmt k1) (fmt v1) (fmt k2) (fmt v2) (fmt k3) (fmt v3))]
    [expr (format "~a" expr)]))

;; transforms higher-level constructs into the core calculus
(define (desugar expr)
  (match expr
    ['⟨⟩ 'sole]
    [`(ref ,e) (desugar `(new ,e))]
    [`(deref ,e) (desugar `(! ,e))]

    [`(set ,e1 ,e2 ,in)
      (desugar `(let _ (: Unit) (set ,e1 ,e2) ,in))]
    [`(let ,id (: ,t) ,e)
      (desugar `(let ,id (: ,t) ,e 'sole))]

    [`(let ,id (: (→ ,k ,a ,b)) (λ ,x ,e) ,in)
      (desugar `((λ ,id (: (→ ,k ,a ,b)) ,in) (λ ,x (: ,a) ,e)))]
    [`(let ,id (: (→ ,a ,b)) (λ ,x ,e) ,in)
      (desugar `((λ ,id (: (→ ,a ,b)) ,in) (λ ,x (: ,a) ,e)))]
    [`(let ,id (: ,t) ,e ,in)
      (desugar `((λ ,id (: ,t) ,in) ,e))]

    [`(letrec ,x (: ,t) ,e ,in)
      (desugar `(let ,x (: ,t) (fix (λ ,x (: ,t) ,e)) ,in))]

    [`(λ ,x (: ,t) ,e) `(λ ,x (: ,t) ,(desugar e))]
    [`(,e1 ,e2 ,e3) `(,(desugar e1) ,(desugar e2) ,(desugar e3))]
    [`(,e1 ,e2) `(,(desugar e1) ,(desugar e2))]
    [e e]))

(provide dbg err note print todo strip fmt desugar)
; todo: how to provide everything??
