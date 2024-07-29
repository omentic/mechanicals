#lang racket
(require (except-in rackunit check))
(require "../stlc-imp.rkt")

(define-test-suite landins-knot
  (check-exn
    exn:fail?
    (λ () (infer '
      (let (id : (Nat → 1 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
      (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
      (set r f
      (f 0))))))))

  (check-eq? ; fixme: this should fail
    (infer '
      (let (id : (Nat → 0 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
      (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
      (f 0)))))
    'Nat)

  (check-true
    (check '
      (let (id : (Nat → 0 Nat)) (λ x x)
      (let (r : (Ref (Nat → 0 Nat))) (new id)
      (let (f : (Nat → 1 Nat)) (λ x ((! r) x))
      (f 0))))
      'Nat)))
