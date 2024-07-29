#lang racket
(require (except-in rackunit check))
(require "../stlc-dll.rkt")

(define-test-suite let-set-inc-case
  (check-exn
    exn:fail?
    (λ () (infer '
      (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
      (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
      (set r f
      (f 0))))))))

  (check-eq?
    (infer '
      (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
      (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
      (f 0)))))
    'Nat)

  (check-eq?
    (check '
      (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 1 Nat))) (new id)
      (let (f : (Nat → 3 Nat)) (λ x ((! r) x))
      (f 0))))
      'Nat)
    #t)

  (check-eq? (interpret '(if #t 1 0)) 1)
  (check-eq? (interpret '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 2)
  (check-eq? (infer '(type Natural Nat ((λ (x : Natural) (inc x)) 1))) 'Nat)
  (check-true (check '(type Natural Nat ((λ (x : Natural) (inc x)) 1)) 'Nat))

  (check-equal?
    (infer
      '(case ((inr sole) : (Nat ⊕ Unit))
        (x ⇒ 0) (x ⇒ 1))) 'Nat)

  (check-true
    (check
      '(case ((inr sole) : (Nat ⊕ Unit))
        (x ⇒ x)
        (x ⇒ 1)) 'Nat))

  (check-equal?
    (interpret
      '((λ p1 (car (unfold p1)))
        (fold
          (pair 413
          (pair (inl sole)
                (inl sole))))))
    413))

;; initial implementation of doubly linked lists:
;; (type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit)))))
(define-test-suite dll-no-empty-lists
  (check-equal?
    (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
     (let get
      (λ x (car (unfold x)))
     (let my_list
      (fold
        (pair 413
        (pair (inl sole)
              (inl sole))))
     (get my_list)))))
    413)

  (check-equal?
    (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
     (let prev
      (λ x
        (case (car (cdr (unfold x)))
          (x ⇒ (inl (! x)))
          (x ⇒ (inr sole))))
     (let my_list
      (fold
        (pair 413
        (pair (inl (new sole))
              (inl (new sole)))))
     (prev my_list)))))
    '(inl sole))

  (check-equal?
    (interpret '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
     (let next
      (λ x
        (case (cdr (cdr (unfold x)))
          (x ⇒ (inl (! x)))
          (x ⇒ (inr sole))))
     (let my_list
      (fold
        (pair 413
        (pair (inr (new sole))
              (inr (new sole)))))
     (next my_list)))))
    '(inr sole))

  (check-true
    (equiv-type
      (infer '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
        (λ (self : DoublyLinkedList)
           (case (cdr (cdr (unfold self)))
            (x ⇒ ((inl (! x)) : (DoublyLinkedList ⊕ Unit)))
            (x ⇒ ((inr sole) : (DoublyLinkedList ⊕ Unit)))))))
      '(DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit))
      #hash((DoublyLinkedList . (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))))))

  (check-true
    (check
      '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
        (λ (self : DoublyLinkedList)
           (case (cdr (cdr (unfold self)))
            (x ⇒ ((inl (! x)) : (DoublyLinkedList ⊕ Unit)))
            (x ⇒ ((inr sole) : (DoublyLinkedList ⊕ Unit))))))
      '(DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit))))

  (check-equal?
    (infer '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
      (let (get : (DoublyLinkedList → 1 Nat))
        (λ self (car (unfold self)))
      (let (prev : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
        (λ self
          (case (car (cdr (unfold self)))
            (x ⇒ (inl (! x)))
            (x ⇒ (inr sole))))
      (let (next : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
        (λ self
          (case (cdr (cdr (unfold self)))
            (x ⇒ (inl (! x)))
            (x ⇒ (inr sole))))
      (let (my_list : DoublyLinkedList)
        (fold
          (pair 413
          (pair ((inr sole) : ((Ref DoublyLinkedList) ⊕ Unit))
                ((inr sole) : ((Ref DoublyLinkedList) ⊕ Unit)))))
      (prev my_list)))))))
    '(DoublyLinkedList ⊕ Unit))

  (check-true
    (check '(type DoublyLinkedList (μ Self (Nat × (((Ref Self) ⊕ Unit) × ((Ref Self) ⊕ Unit))))
      (let (get : (DoublyLinkedList → 1 Nat))
        (λ self (car (unfold self)))
      (let (prev : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
        (λ self
          (case (car (cdr (unfold self)))
            (x ⇒ (inl (! x)))
            (x ⇒ (inr sole))))
      (let (next : (DoublyLinkedList → 1 (DoublyLinkedList ⊕ Unit)))
        (λ self
          (case (cdr (cdr (unfold self)))
            (x ⇒ (inl (! x)))
            (x ⇒ (inr sole))))
      (let (my_list : DoublyLinkedList)
        (fold
          (pair 413
          (pair ((inr sole) : ((Ref DoublyLinkedList) ⊕ Unit))
                ((inr sole) : ((Ref DoublyLinkedList) ⊕ Unit)))))
      (prev my_list))))))
      '(DoublyLinkedList ⊕ Unit))))

;; new implementation of doubly linked lists:
;; (type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)))
(define-test-suite dll-with-empty-lists
  (check-equal?
    (interpret
     '(let next
      (λ self
        (case (unfold self)
          (some ⇒ (! (cdr (cdr some))))
          (none ⇒ (fold (inr sole)))))
     (let my_list
      (fold
        (inl
          (pair 413
          (pair (new (inr sole))
                (new (inr sole))))))
     (next my_list))))
    '(inr sole))

  (check-equal?
    (infer '(type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
      (λ (self : DoublyLinkedList)
         (case (unfold self)
          (some ⇒ ((! (cdr (cdr some))) : DoublyLinkedList))
          (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))))
    '((μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit)) → 1 (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))))

  (check-true
    (equiv-type
      (infer '(type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
        (λ (self : DoublyLinkedList)
           (case (unfold self)
            (some ⇒ (! (cdr (cdr some))))
            (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))))
    '(DoublyLinkedList → 1 DoublyLinkedList)
      #hash((DoublyLinkedList . (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))))))

  (check-true
    (check '(type DoublyLinkedList (μ Self ((Nat × ((Ref Self) × (Ref Self))) ⊕ Unit))
      (let (get : (DoublyLinkedList → 1 (Nat ⊕ Unit)))
        (λ self
          (case (unfold self)
            (some ⇒ (inl (car some)))
            (none ⇒ (inr sole))))
      (let (prev : (DoublyLinkedList → 1 DoublyLinkedList))
        (λ self
          (case (unfold self)
            (some ⇒ (! (car (cdr some))))
            (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))
      (let (next : (DoublyLinkedList → 1 DoublyLinkedList))
        (λ self
          (case (unfold self)
            (some ⇒ (! (cdr (cdr some))))
            (none ⇒ ((fold (inr sole)) : DoublyLinkedList))))
      (let (my_list : DoublyLinkedList)
        (fold (inl
          (pair 413
          (pair (new ((fold (inr sole)) : DoublyLinkedList))
                (new ((fold (inr sole)) : DoublyLinkedList))))))
      (prev my_list))))))
      'DoublyLinkedList)))
