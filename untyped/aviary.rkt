#lang racket
(provide (all-defined-out))

;; Encodings of various combinators in s-exps
;; https://www.angelfire.com/tx4/cus/combinator/birds.html
;; https://wiki.xxiivv.com/site/ornithodex.html

;; Bluebird
(define B  '(λ a (λ b (λ c (a (b c))))))
;; Blackbird
(define B1 '(λ a (λ b (λ c (λ d (a ((b c) d)))))))
;; Bunting
(define B2 '(λ a (λ b (λ c (λ d (λ e (a (((b c) d) e))))))))
;; Becard
(define B3 '(λ a (λ b (λ c (λ d (a (b (c d))))))))
;; Cardinal
(define C  '(λ a (λ b (λ c ((a c) b)))))
;; Dove
(define D  '(λ a (λ b (λ c (λ d ((a b) (c d)))))))
;; Dickcissel
(define D1 '(λ a (λ b (λ c (λ d (λ e (((a b) c) (d e))))))))
;; Dovekies
(define D2 '(λ a (λ b (λ c (λ d (λ e ((a (b c)) (d e))))))))
;; Eagle
(define E  '(λ a (λ b (λ c (λ d (λ e ((a b) ((c d) e))))))))
;; Bald Eagle
(define Ê  '(λ a (λ b (λ c (λ d (λ e (λ f (λ g ((a ((b c) d)) ((e f) g))))))))))
;; Finch
(define F  '(λ a (λ b (λ c ((c b) a)))))
;; Goldfinch
(define G  '(λ a (λ b (λ c (λ d ((a d) (b c)))))))
;; Hummingbird
(define H  '(λ a (λ b (λ c (((a b) c) b)))))
;; Idiot Bird (Identity)
(define I  '(λ a a))
;; Jay
(define J  '(λ a (λ b (λ c (λ d ((a b) ((a d) c)))))))
;; Kestrel (True)
(define K  '(λ a (λ b a)))
;; Kite (False)
(define Ki '(λ a (λ b b)))
;; Lark
(define L  '(λ a (λ b (a (b b)))))
;; Nightingale
(define N  '(λ a (λ b (λ c (λ d ((a (b d)) (c d)))))))
;; Mockingbird
(define M  '(λ a (a a)))
;; Double Mockingbird
(define M2 '(λ a (λ b ((a b) (a b)))))
;; Owl
(define O  '(λ a (λ b (b (a b)))))
;; Queer Bird
(define Q  '(λ a (λ b (λ c (b (a c))))))
;; Quixotic Bird
(define Q1 '(λ a (λ b (λ c (a (c b))))))
;; Quizzical Bird
(define Q2 '(λ a (λ b (λ c (b (c a))))))
;; Quirky Bird
(define Q3 '(λ a (λ b (λ c (c (a b))))))
;; Quacky Bird
(define Q4 '(λ a (λ b (λ c (c (b a))))))
;; Robin
(define R  '(λ a (λ b (λ c ((b c) a)))))
;; Starling
(define S  '(λ a (λ b (λ c ((a c) (b c))))))
;; Thrush
(define T  '(λ a (λ b (b a))))
;; Turing
(define U  '(λ a (λ b (b ((a a) b)))))
;; Vireo (aka Pairing)
(define V  '(λ a (λ b (λ c ((c a) b)))))
;; Warbler
(define W  '(λ a (λ b ((a b) b))))
;; Converse Warbler
(define W1 '(λ a (λ b ((b a) a))))
;; Why Bird (aka Sage Bird)
(define Y  '(λ a (a (λ a todo))))
;; Idiot Bird Once Removed
(define I* '(λ a (λ b (a b))))
;; Warbler Once Removed
(define W* '(λ a (λ b (λ c (((a b) c) c)))))
;; Cardinal Once Removed
(define C* '(λ a (λ b (λ c (λ d (((a b) d) c))))))
;; Robin Once Removed
(define R* '(λ a (λ b (λ c (λ d (((a c) d) b))))))
;; Finch Once Removed
(define F* '(λ a (λ b (λ c (λ d (((a d) c) b))))))
;; Vireo Once Removed
(define V* '(λ a (λ b (λ c (λ d (((a c) b) d))))))
;; Warbler Twice Removed
(define W** '(λ a (λ b (λ c (λ d ((((a b) c) d) d))))))
;; Cardinal Twice Removed
(define C** '(λ a (λ b (λ c (λ d (λ e ((((a b) c) e) d)))))))
;; Robin Twice Removed
(define R** '(λ a (λ b (λ c (λ d (λ e ((((a b) d) e) c)))))))
;; Finch Twice Removed
(define F** '(λ a (λ b (λ c (λ d (λ e ((((a b) e) d) c)))))))
;; Vireo Twice Removed
(define V** '(λ a (λ b (λ c (λ d (λ e ((((a b) e) c) d)))))))
;; Konstant Mocker
(define KM  '(λ a (λ b (b b))))
;; Crossed Konstant Mocker
(define CKM '(λ a (λ b (a a))))
