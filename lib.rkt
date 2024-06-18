#lang racket
(require rackunit)
(require syntax/location)
(require (for-syntax syntax/location))
(provide (all-defined-out))

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
    [`(,e1 ,e2 ,e3 ,e4) `(,(strip e1) ,(strip e2) ,(strip e3) ,(strip e4))]
    [`(,e1 ,e2 ,e3) `(,(strip e1) ,(strip e2) ,(strip e3))]
    [`(,e1 ,e2) `(,(strip e1) ,(strip e2))]
    [e e]))

;;      (fmt Expr) → String
(define (fmt expr)
  (match expr
    ['sole "⟨⟩"]
    [`(λ ,x ,e) (format "λ~a.[~a]" x (fmt e))]
    [`((λ ,x ,e1) ,e2) (format "~a = ~a; ~a" x (fmt e2) (fmt e1))]
    [`(λ ,x (: ,t) ,e) (format "~a: ~a; ~a" x (fmt t) (fmt e))]
    [`((λ ,x (: ,t) ,e1) ,e2) (format "~a: ~a; ~a = ~a; ~a" x (fmt t) x (fmt e2) (fmt e1))]
    [`(λ ,x ,e ,env) (format "λ~a.[~a]" x (fmt e))]
    [`(μ ,x ,t) (format "μ~a.~a" x (fmt t))]
    [`(let ,x ,e ,in) (format "~a = ~a; ~a" x (fmt e) (fmt in))]
    [`(let ,x (: ,t) ,e ,in) (format "~a: ~a; ~a = ~a; ~a" x (fmt t) x (fmt e) (fmt in))]
    [`(set ,x ,e ,in) (format "~a := ~a; ~a" x (fmt e) (fmt in))]
    [`(→ ,a ,b) (format "(~a → ~a)" (fmt a) (fmt b))]
    [`(→ ,k ,a ,b) (format "(~a →~a ~a)" (fmt a) k (fmt b))]
    [`(Ref ,a) (format "Ref ~a" (fmt a))]
    [`(new ,a) (format "new ~a" (fmt a))]
    [`(! ,a) (format "!~a" (fmt a))]
    [`(,a ,b) (format "(~a ~a)" (fmt a) (fmt b))]
    [(hash-table (keys values) ...)
      (format "{~a}" (foldl (λ (k v acc) (format "~a: ~a;" (fmt k) (fmt v))) "" keys values))]
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
      (desugar `(let ,id (: ,t) ,e sole))]

    [`(let ,id (: (→ ,k ,a ,b)) (λ ,x ,e) ,in)
      (desugar `((λ ,id (: (→ ,k ,a ,b)) ,in) (λ ,x (: ,a) ,e)))]
    [`(let ,id (: (→ ,a ,b)) (λ ,x ,e) ,in)
      (desugar `((λ ,id (: (→ ,a ,b)) ,in) (λ ,x (: ,a) ,e)))]
    [`(let ,id (: ,t) ,e ,in)
      (desugar `((λ ,id (: ,t) ,in) ,e))]

    [`(letrec ,x (: ,t) ,e ,in)
      (desugar `(let ,x (: ,t) (fix (λ ,x (: ,t) ,e)) ,in))]

    [`(λ ,x (: ,t) ,e) `(λ ,x (: ,t) ,(desugar e))]
    [`(,e1 ,e2 ,e3 ,e4) `(,(desugar e1) ,(desugar e2) ,(desugar e3) ,(desugar e4))]
    [`(,e1 ,e2 ,e3) `(,(desugar e1) ,(desugar e2) ,(desugar e3))]
    [`(,e1 ,e2) `(,(desugar e1) ,(desugar e2))]
    [e e]))

(define (char-inc c) (integer->char (inc (char->integer c))))
(define (char->string c) (list->string (list c)))
(define (symbol->list s) (string->list (symbol->string s)))
(define (list->symbol l) (string->symbol (list->string l)))
(define (symbol-append a b) (string->symbol (string-append (symbol->string a) (symbol->string b))))

;; provides a "pretty" gensym: 'a -> 'b, 'z -> 'aa, 'az -> 'ba etc. quite inefficient.
(define (fresh used)
  (cond
    [(list? used) (fresh-helper '|| (list->set used))]
    [(symbol? used) (fresh-helper '|| (set used))]
    [(set? used) (fresh-helper '|| used)]))
(define (fresh-helper prev used)
  (let ([new (fresh-next prev)])
    (if (set-member? used new) (fresh-helper new used) new)))
(define (fresh-next prev)
  (if (equal? prev '||) 'a
    (let ([prev (reverse (symbol->list prev))])
    (if (zero? (length prev)) '||
      (match (first prev)
        [#\z (symbol-append (fresh-next (list->symbol (reverse (rest prev)))) 'a)]
        [c (list->symbol (reverse (cons (char-inc c) (rest prev))))])))))
(check-equal? (fresh-next 'a) 'b)
(check-equal? (fresh-next 'zaa) 'zab)
(check-equal? (fresh-next 'azz) 'baa)

;; checks if two expressions are equivalent up to α-renaming
(define (equiv? e1 e2 [ctx1 #hash()] [ctx2 #hash()])
  (match* (e1 e2)
    [(x1 x2) #:when (dict-has-key? ctx1 x1)
      (equiv? (dict-ref ctx1 x1) x2 ctx1 ctx2)]
    [(x1 x2) #:when (dict-has-key? ctx2 x2)
      (equiv? x1 (dict-ref ctx2 x2) ctx1 ctx2)]
    [(`(λ ,x1 (: _) ,e1) `(λ ,x2 (: _) ,e2)) ; todo: merge these into one
      (let ([name gensym])
      (equiv? e1 e2 (dict-set ctx1 x1 name) (dict-set ctx2 x2 name)))]
    [(`(λ ,x1 ,e1) `(λ ,x2 ,e2))
      (let ([name gensym])
      (equiv? e1 e2 (dict-set ctx1 x1 name) (dict-set ctx2 x2 name)))]
    [(`(,l1 ...) `(,l2 ...))
      (foldl (λ (x1 x2 acc) (if (equiv? x1 x2 ctx1 ctx2) acc #f)) #t l1 l2)]
    [(v1 v2) (equal? v1 v2)]))
(check-true (equiv? '(λ a a) '(λ b b)))
(check-true (equiv? '(λ a (λ b a)) '(λ b (λ a b))))
(check-true (equiv? '(λ a (λ b (λ c (a (b c))))) '(λ c (λ a (λ b (c (a b)))))))

;; normalizes an expression into binding variables descending
;;      (α-convert Expr Table[Old New] Set[New])
(define (α-convert expr [used #hash()])
  (match expr
    [x #:when (dict-has-key? used x) (dict-ref used x)]
    [`(λ ,x (: ,t) ,e)
      (let ([new (fresh (dict-values used))])
      `(λ ,new (: ,(α-convert t used)) ,(α-convert e (dict-set used x new))))]
    [`(λ ,x ,e)
      (let ([new (fresh (dict-values used))])
      `(λ ,new ,(α-convert e (dict-set used x new))))]
    [`(μ ,x ,t)
      (let ([new (fresh (dict-values used))])
      `(μ ,new ,(α-convert t (dict-set used x new))))]
    [`(,e ...) (map (λ (x) (α-convert x used)) e)]
    [v v]))
(check-equal? '(λ a (λ b (λ c (a (b c)))))
  (α-convert '(λ a (λ b (λ c (a (b c)))))))
(check-equal? '(λ a (λ b (λ c (a (b c)))))
  (α-convert '(λ c (λ a (λ b (c (a b)))))))
