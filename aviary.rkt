#lang racket
; note: bad error message on lacking #lang racket
; default-load-handler: expected a `module' declaration, but found something else

;; Encodings of various combinators in s-exps
;; https://www.angelfire.com/tx4/cus/combinator/birds.html
;; https://wiki.xxiivv.com/site/ornithodex.html

(define B  '(λ a (λ b (λ c (a (b c)))))) ; Bluebird
(define B1 '(λ a (λ b (λ c (λ d (a ((b c) d))))))) ; Blackbird
(define B2 '(λ a (λ b (λ c (λ d (λ e (a (((b c) d) e)))))))) ; Bunting
(define B3 '(λ a (λ b (λ c (λ d (a (b (c d)))))))) ; Becard
(define C  '(λ a (λ b (λ c ((a c) b))))) ; Cardinal
(define D  '(λ a (λ b (λ c (λ d ((a b) (c d))))))) ; Dove
(define D1 '(λ a (λ b (λ c (λ d (λ e (((a b) c) (d e)))))))) ; Dickcissel
(define D2 '(λ a (λ b (λ c (λ d (λ e ((a (b c)) (d e)))))))) ; Dovekies
(define E  '(λ a (λ b (λ c (λ d (λ e ((a b) ((c d) e)))))))) ; Eagle
(define Ê  '(λ a (λ b (λ c (λ d (λ e (λ f (λ g ((a ((b c) d)) ((e f) g)))))))))) ; Bald Eagle
(define F  '(λ a (λ b (λ c ((c b) a))))) ; Finch
(define G  '(λ a (λ b (λ c (λ d ((a d) (b c))))))) ; Goldfinch
(define H  '(λ a (λ b (λ c (((a b) c) b))))) ; Hummingbird
(define I  '(λ a a)) ; Idiot Bird (Identity)
(define J  '(λ a (λ b (λ c (λ d ((a b) ((a d) c))))))) ; Jay
(define K  '(λ a (λ b a))) ; Kestrel (True)
(define Ki '(λ a (λ b b))) ; Kite (False)
(define L  '(λ a (λ b (a (b b))))) ; Lark
(define N  '(λ a (λ b (λ c (λ d ((a (b d)) (c d))))))) ; Nightingale
(define M  '(λ a (a a))) ; Mockingbird
(define M2 '(λ a (λ b ((a b) (a b))))) ; Double Mockingbird
(define O  '(λ a (λ b (b (a b))))) ; Owl
(define Q  '(λ a (λ b (λ c (b (a c)))))) ; Queer Bird
(define Q1 '(λ a (λ b (λ c (a (c b)))))) ; Quixotic Bird
(define Q2 '(λ a (λ b (λ c (b (c a)))))) ; Quizzical Bird
(define Q3 '(λ a (λ b (λ c (c (a b)))))) ; Quirky Bird
(define Q4 '(λ a (λ b (λ c (c (b a)))))) ; Quacky Bird
(define R  '(λ a (λ b (λ c ((b c) a))))) ; Robin
(define S  '(λ a (λ b (λ c ((a c) (b c)))))) ; Starling
(define T  '(λ a (λ b (b a)))) ; Thrush
(define U  '(λ a (λ b (b ((a a) b))))) ; Turing
(define V  '(λ a (λ b (λ c ((c a) b))))) ; Vireo (aka Pairing)
(define W  '(λ a (λ b ((a b) b)))) ; Warbler
(define W1 '(λ a (λ b ((b a) a)))) ; Converse Warbler
(define Y  '(λ a (a (λ a todo)))) ; Why Bird (aka Sage Bird)
(define I* '(λ a (λ b (a b)))) ; Idiot Bird Once Removed
(define W* '(λ a (λ b (λ c (((a b) c) c))))) ; Warbler Once Removed
(define C* '(λ a (λ b (λ c (λ d (((a b) d) c)))))) ; Cardinal Once Removed
(define R* '(λ a (λ b (λ c (λ d (((a c) d) b)))))) ; Robin Once Removed
(define F* '(λ a (λ b (λ c (λ d (((a d) c) b)))))) ; Finch Once Removed
(define V* '(λ a (λ b (λ c (λ d (((a c) b) d)))))) ; Vireo Once Removed
(define W** '(λ a (λ b (λ c (λ d ((((a b) c) d) d)))))) ; Warbler Twice Removed
(define C** '(λ a (λ b (λ c (λ d (λ e ((((a b) c) e) d))))))) ; Cardinal Twice Removed
(define R** '(λ a (λ b (λ c (λ d (λ e ((((a b) d) e) c))))))) ; Robin Twice Removed
(define F** '(λ a (λ b (λ c (λ d (λ e ((((a b) e) d) c))))))) ; Finch Twice Removed
(define V** '(λ a (λ b (λ c (λ d (λ e ((((a b) e) c) d))))))) ; Vireo Twice Removed
(define KM  '(λ a (λ b (b b)))) ; Konstant Mocker KM
(define CKM '(λ a (λ b (a a)))) ; Crossed Konstant Mocker

(provide
  B B1 B2 B3 C D D1 D2 E Ê F G H I J K Ki L N M M2 O Q Q1 Q2 Q3 Q4 R S T U V W W1 Y
  I* W* C* R* F* V* W** C** R** F** V** KM CKM)

(require rackunit "lc.rkt")
; FIXME: all of these fail
(check-equal? (normalize `((,S (,K ,S)) ,K)) B)
(check-equal? (normalize `((,B ,B) ,B)) B1)
(check-equal? (normalize `((,B ((,B ,B) ,B)) ,B)) B2)
(check-equal? (normalize `((,B (,B ,B)) ,B)) B3)
; (check-equal? (normalize `((,S ((,B ,B) ,S)) (,K ,K))) C)
; (check-equal? (normalize `(,B ,B)) D)
; (check-equal? (normalize `(,B (,B ,B))) D1)
; (check-equal? (normalize `((,B ,B) (,B ,B))) D2)
; (check-equal? (normalize `(,B ((,B ,B) ,B))) E)
(check-equal? (normalize `((,B ((,B ,B) ,B)) (B ((B B) B)))) Ê)
(check-equal? (normalize `((((,E ,T) ,T) ,E) ,T)) F)
(check-equal? (normalize `((,B ,B) ,C)) G)
(check-equal? (normalize `((,B ,W) (,B ,C))) H)
(check-equal? (normalize `((,S ,K) ,K)) I)
(check-equal? (normalize `((,B (,B ,C)) (,W ((,B ,C) (,B ((,B ,B) ,B)))))) J)
(check-equal? (normalize `((,C ,B) ,M)) L)
(check-equal? (normalize `((,B (,B ,S)) ,B)) N)
(check-equal? (normalize `((,S ,I) ,I)) M)
; (check-equal? (normalize `(,B ,M)) M2)
(check-equal? (normalize `(,S ,I)) O)
(check-equal? (normalize `(,C ,B)) Q)
(check-equal? (normalize `((,B ,C) ,B)) Q1)
(check-equal? (normalize `(,C ((,B ,C) ,B))) Q2)
; (check-equal? (normalize `(,B ,T)) Q3)
(check-equal? (normalize `(,F* ,B)) Q4)
(check-equal? (normalize `((,B ,B) ,T)) R)
(check-equal? S S)
(check-equal? (normalize `(,C ,I)) T)
; (check-equal? (normalize `(,L ,O)) U)
(check-equal? (normalize `((,B ,C) ,T)) V)
(check-equal? (normalize `(,C ((,B ,M) ,R))) W)
(check-equal? (normalize `(,C ,W)) W1)
(check-equal? (normalize `((,S ,L) ,L)) Y)
(check-equal? (normalize `(,S (,S ,K))) I*)
(check-equal? (normalize `(,B ,W)) W*)
(check-equal? (normalize `(,B ,C)) C*)
(check-equal? (normalize `(,C* ,C*)) R*)
(check-equal? (normalize `((,B ,C*) ,R*)) F*)
(check-equal? (normalize `(,C* ,F*)) V*)
; (check-equal? (normalize `(,B (,B ,W))) W**)
(check-equal? (normalize `(,B ,C*)) C**)
(check-equal? (normalize `(,B ,R*)) R**)
(check-equal? (normalize `(,B ,F*)) F**)
(check-equal? (normalize `(,B ,V*)) V**)
(check-equal? KM KM)
(check-equal? (normalize `(,C (,K ,M))) CKM)
