#lang racket
(require rackunit)
(require racket/trace)
(require syntax/location)
(require (for-syntax syntax/location))
(provide (all-defined-out) trace)

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

(define (any? proc lst)
  (foldl (λ (x acc) (if (proc x) #t acc)) #f lst))

(define (all? proc lst)
  (foldl (λ (x acc) (if (proc x) acc #f)) #t lst))

(define (inc i) (+ i 1))
(define (dec i) (- i 1))

(define (char-inc c) (integer->char (inc (char->integer c))))
(define (char->string c) (list->string (list c)))
(define (symbol->list s) (string->list (symbol->string s)))
(define (list->symbol l) (string->symbol (list->string l)))
(define (symbol-append a b) (string->symbol (string-append (symbol->string a) (symbol->string b))))

;; Provides a "pretty" gensym: 'a -> 'b, 'z -> 'aa, 'az -> 'ba etc.
;; quite inefficient.
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

;; Normalizes an expression into binding variables descending
;;      (α-convert Expr Table[Old New] Set[New])
(define (α-convert expr [used #hash()])
  (match expr
    [x #:when (dict-has-key? used x) (dict-ref used x)]
    [`(λ (,x : ,t) ,e)
      (let ([new (fresh (dict-values used))])
      `(λ (,new : ,(α-convert t used)) ,(α-convert e (dict-set used x new))))]
    [`(λ ,x ,e)
      (let ([new (fresh (dict-values used))])
      `(λ ,new ,(α-convert e (dict-set used x new))))]
    [`(μ ,x ,t)
      (let ([new (fresh (dict-values used))])
      `(μ ,new ,(α-convert t (dict-set used x new))))]
    [`(,e ...) `(,@(map (λ (x) (α-convert x used)) e))]
    [v v]))
(check-equal? '(λ a (λ b (λ c (a (b c)))))
  (α-convert '(λ a (λ b (λ c (a (b c)))))))
(check-equal? '(λ a (λ b (λ c (a (b c)))))
  (α-convert '(λ c (λ a (λ b (c (a b)))))))
