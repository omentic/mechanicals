#lang racket
(require "lib.rkt")

;; The Simply-Typed Lambda Calculus with higher-order *predicative* references

;;      (interpret Expr Table[Sym, Expr]) → Value
(define (interpret expr [ctx #hash()] [heap (make-hash)])
  (interpret- (strip (desugar expr)) ctx heap))
(define (interpret- expr ctx heap)
  (match expr
    [x #:when (dict-has-key? ctx x) (dict-ref ctx x)] ; x
    [x #:when (dict-has-key? heap x) x] ; todo
    [n #:when (natural? n) n]                     ; n
    ['⟨⟩ '⟨⟩]                                      ; ⟨⟩

    [`(λ ,id ,body) `(λ ,id ,body ,ctx)]          ; λx:τ.e

    [`(new ,expr)                                 ; new e
      (let ([address (gensym)])
        (dict-set! heap address expr) address)]
    [`(! ,id)                                     ; !e
      (let ([id (interpret- id ctx heap)])
        (if (dict-has-key? heap id)
          (interpret- (dict-ref heap id) ctx heap)
          (err (format "attempting to deref unknown reference ~a" id))))]
    [`(set ,id ,expr)                             ; e := e
      (let ([id (interpret- id ctx heap)])
        (if (dict-has-key? heap id)
          (dict-set! heap id (interpret- expr ctx heap))
          (err (format "attempting to update unknown reference ~a" id))))
      '⟨⟩]

    [`(,body ,arg)                                ; e e
      (match (interpret- body ctx heap)
        [`(λ ,id ,body ,env)
          (interpret- body (dict-set env id (interpret- arg ctx heap)) heap)]
        [expr (err (format "attempting to interpret arg ~a applied to unknown expression ~a" arg expr))])]

    [expr (err (format "interpreting an unknown expression ~a" expr))]))

;; transforms higher-level constructs into the core calculus
(define (desugar expr)
  (match expr
    ['sole '⟨⟩]
    [`(ref ,expr) (desugar `(new ,expr))]
    [`(deref ,expr) (desugar `(! ,expr))]
    [`(set ,id ,expr ,body)
      (desugar `(let _ (set ,id ,expr) ,body))]

    [`(let ,id (: (→ ,k ,a ,b)) (λ ,x ,e) ,body)
      (desugar `((λ ,id (: (→ ,k ,a ,b)) ,body) (λ ,x (: ,a) ,e)))]
    [`(let ,id (: (→ ,a ,b)) ,expr ,body)
      (err "you forgot to add a level annotation dummy")]
    [`(let ,id (: ,type) ,e ,body)
      (desugar `((λ ,id (: ,type) ,body) ,e))]
    [`(let ,id (: ,type) ,expr)
      (desugar `(let ,id (: ,type) ,expr '⟨⟩))]

    [`(new ,expr) `(new ,(desugar expr))]
    [`(! ,expr) `(! ,(desugar expr))]
    [`(set ,id ,expr) `(set ,(desugar id) ,(desugar expr))]
    [`(λ ,id (: ,type) ,expr) `(λ ,id (: ,type) ,(desugar expr))]
    [`(,body ,arg) `(,(desugar body) ,(desugar arg))]
    [id #:when (number? id) id]
    [id #:when (symbol? id) id]

    [expr (err (format "desugaring unknown expression ~a" expr))]))

;; removes typing annotations
(define (strip expr)
  (match expr
    [`(λ ,id (: ,type) ,body (: ,type)) `(λ ,(strip id) ,(strip body))]
    [`(λ ,id ,body (: ,type)) `(λ ,(strip id) ,(strip body))]
    [`(λ ,id (: ,type) ,body) `(λ ,(strip id) ,(strip body))]
    [`(,a ,b) `(,(strip a) ,(strip b))]
    [expr expr]))

;;      (check Expr Type Table[Sym, Type]): Bool
(define (check expr with [Γ #hash()])
  (check- (desugar expr) with Γ))
(define (check- expr with Γ)
  ; (print (format "check: ~a" (fmt expr)))
  (match* (expr with)
    [(n 'Nat) #:when (natural? n) #t]       ; ↝ Γ ⊢ n: Nat
    [('⟨⟩ 'Unit) #t]                         ; ↝ Γ ⊢ ⟨⟩: Unit
    [(x _) #:when (dict-has-key? Γ x)        ; x: τ ∈ Γ → Γ ⊢ x: τ
      (equal? (dict-ref Γ x) with)]

    [(`(new ,e) `(Ref ,τ)) (check- e τ Γ)]  ; Γ ⊢ e: τ → Γ ⊢ new e: Ref τ
    [(`(! ,e) τ) (check- e `(Ref ,τ) Γ)]    ; Γ ⊢ e: Ref τ → Γ ⊢ !e: τ
    [(`(set ,e1 ,e2) 'Unit)                 ; ↝ Γ ⊢ e1 := e2: Unit
      (match (infer- e1 Γ)
        [`(Ref ,τ) (check- e2 τ Γ)]         ; Γ ⊢ e1: Ref τ, Γ ⊢ e2: τ
        [type (err (format "attempting to update non-reference ~a: ~a" e1 type))])]

    [(`(λ ,x (: ,τ) ,e) `(→ ,k ,τ1 ,τ2))    ; ↝ Γ ⊢ λx: τ1.e: τ1 →k τ2
      (and
        (equal? τ τ1)
        (>= k (max-level e (dict-set Γ x τ1) τ1 τ2))  ; k ≥ max-level(Γ, τ1, τ2) (KNOB)
        (check- e τ2 (dict-set Γ x τ1)))]             ; Γ, x: τ1 ⊢ e: τ2

    [(`(,e1 ,e2) τ)                                   ; ↝ Γ ⊢ (e1 e2): τ2
      (match (infer- e1 Γ)
        [`(→ ,k ,τ1 ,τ2)                              ; Γ ⊢ e1: τ1 →k τ2
          (and (equal? τ2 τ)                          ; Γ ⊢ e2: τ1
               (equal? τ1 (infer- e2 Γ)))]
        [type (err (format "expected → type on application body, got ~a" type))])]

    [(`(λ ,id (: ,type) ,body) `(→ ,a ,b)) ; error handling
      (err "you forgot to add a level annotation dummy")]
    [(expr _) (err (format "checking an unknown expression ~a with type ~a" expr with))]))

;;      (infer Expr Table[Sym, Type]) → Type
(define (infer expr [Γ #hash()])
  (infer- (desugar expr) Γ))
(define (infer- expr Γ)
  ; (print (format "infer: ~a" (fmt expr)))
  (match expr
    ['⟨⟩ 'Unit]                          ; ↝ Γ ⊢ ⟨⟩: Unit
    [n #:when (natural? n) 'Nat]        ; ↝ Γ ⊢ n: Nat
    [x #:when (dict-has-key? Γ x)       ; x: τ ∈ Γ
      (dict-ref Γ x)]                   ; ↝ Γ ⊢ x: τ

    [`(new ,e) `(Ref ,(infer- e Γ))]    ; Γ ⊢ e: τ → Γ ⊢ new e: Ref τ
    [`(! ,e)
      (match (infer- e Γ)
        [`(Ref ,type) type]             ; Γ ⊢ e: Ref τ → Γ ⊢ !e: τ
        [_ (err "attempting to deref term not of Ref type!")])]
    [`(set ,e1 ,e2)
      (match (infer- e1 Γ)
        [`(Ref ,τ)                       ; Γ ⊢ e1: Ref τ, Γ ⊢ e2: τ
          (if (check- e2 τ Γ) 'Unit      ; ↝ Γ ⊢ e1 := e2: Unit
            (err (format "attempting to update ~a: ~a with term ~a: ~a of differing type"
              e1 τ e2 (infer- e2 Γ))))]
        [type (err (format "attempting to update non-reference ~a: ~a" e1 type))])]

    [`(λ ,x (: ,τ1) ,e)
      (let ([τ2 (infer- e (dict-set Γ x τ1))])            ; Γ, x: τ1 ⊢ e: τ2
        (let ([k (max-level e (dict-set Γ x τ1) τ1 τ2)])  ; k ≥ max-level(Γ, τ1, τ2) (KNOB)
          `(→ ,k ,τ1 ,τ2)))]                              ; ↝ Γ ⊢ λx: τ1.e: τ1 →k τ2

    [`(,e1 ,e2)
      (match (infer- e1 Γ)
        [`(→ ,k ,τ1 ,τ2)                                  ; Γ ⊢ e1: τ1 →k τ2
          (if (check- e2 τ1 Γ)                            ; Γ ⊢ e2: τ1
            τ2                                            ; ↝ Γ ⊢ (e1 e2): τ2
            (err (format "inferred argument type ~a does not match arg ~a" τ1 e2)))]
        [type (err (format "expected → type on application body, got ~a" type))])]

    [`(λ ,x ,e) ; error handling
      (err "unable to infer type from λ lacking parameter annotation")]
    [expr (err (format "inferring an unknown expression ~a" expr))]))

;;      (max-level Table[Sym, Type] Expr Type Type) → Natural
(define (max-level e Γ τ1 τ2)
  (max
    (level-type τ1)
    (level-type τ2)
    (level-body e Γ)))

;;      (level-type Type) → Natural
(define (level-type τ)
  (match τ
    ['Unit 0]
    ['Nat 0]
    [`(→ ,k ,τ1 ,τ2)
      (if (or (< k (level-type τ1)) (< k (level-type τ2)))
        (err (format "annotated level ~a is less than inferred levels of ~a and ~a!"
          k τ1 τ2))
        k)]
    [`(Ref ,τ) (+ 1 (level-type τ))] ; (KNOB)
    [τ (err (format "inferring the level of unknown type ~a" τ))]))

;;      (level-body Expr Table[Sym, Type]) → Natural
(define (level-body e Γ)
  (match e
    ['⟨⟩ 0]
    [n #:when (natural? n) 0]
    [x #:when (dict-has-key? Γ x)
      (level-type (dict-ref Γ x))]
    [`(new ,e) (level-body e Γ)]
    [`(! ,e) (level-body e Γ)]
    [`(set ,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]
    [`(λ ,x (: ,τ) ,e) (level-body e (dict-set Γ x τ))] ; todo: should be 0?
    [`(,e1 ,e2) (max (level-body e1 Γ) (level-body e2 Γ))]))

;;      (fmt Expr) → String
(define (fmt expr)
  (match expr
    ['⟨⟩ "⟨⟩"]
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

; simple diverging program in STLC-ref
; https://www.youtube.com/watch?v=XNgE8kBfSz8
#;
(interpret '
  (let id (: (→ 0 Nat Nat)) (λ x x)
    (let r (: (Ref (→ 0 Nat Nat))) (ref id)
      (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0))))))
#;
(print (fmt '
  (let id (: (→ 0 Nat Nat)) (λ x x)
    (let r (: (Ref (→ 0 Nat Nat))) (ref id)
      (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
        (set r f
          (f 0)))))))

(require rackunit)
(check-exn
  exn:fail?
  (λ () (infer '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (set r f
            (f 0))))))))

(check-eq?
  (infer '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (f 0)))))
  'Nat)

(check-eq?
  (check '
    (let id (: (→ 0 Nat Nat)) (λ x x)
      (let r (: (Ref (→ 0 Nat Nat))) (ref id)
        (let f (: (→ 1 Nat Nat)) (λ x ((deref r) x))
          (f 0))))
    'Nat)
  #t)
