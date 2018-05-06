;;normalize.scm
;;20180501Z
;;jpt4
;;Reduce arbitrary SL expression to disjunctive normal form

(load "miniKanren-with-symbolic-constraints/mk.scm")

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//)])
  )

(define (variable s) (simple-statement s))

(define (dnf-diso? s)
  (fresh (c d)
         (conde
          [(== `(// ,c ,d) s) (dnf-conjo? c) (dnf-diso? d)]
          [(dnf-conjo? s)])))

(define (dnf-conjo? s)
  (fresh (l c)
         (conde
          [(== `(& ,l ,c) s) (lito? l) (dnf-conjo? c)]
          [(lito? s)])))

(define (lito? s)
  (fresh (v)
         (conde
          [(== `(~ ,v) s) (variable v)]
          [(variable s)])))
  
(define (dnfo? s) (dnf-diso? s))

(define (cnf-conjo? s)
  (fresh (c d)
         (conde
          [(== `(& ,d ,c) s) (cnf-diso? d) (cnf-conjo? c)]
          [(cnf-diso? s)])))

(define (cnf-diso? s)
  (fresh (l d)
         (conde
          [(== `(// ,l ,d) s) (lito? l) (cnf-diso? d)]
          [(lito? s)])))

(define (cnfo? s) (cnf-conjo? s))

(define (cnfo i o)
  (fresh (p q r resp resq resr resi)
         (conde
	  [(ground-termo? i) (== i o)]
	  [(cnfo? i) (== i o)]
	  [(== `(~ ,p) i) (== `(~ ,resp) o) (cnfo resp p)]
	  [(== `(// ,p ,q) i) (== `(// ,resp ,resq) o) (cnfo resp p) (cnfo resq q)]
	  [(== `(& ,p ,q) i) (== `(& ,resp ,resq) o) (cnfo resp p) (cnfo resq q)]
	  [(== `(~ (~ ,p)) i) (== resp o) (cnfo p resp)]
          [(== `(-> ,p ,q) i) (== `(// (~ ,resp) ,resq) o) (cnfo p resp) (cnfo q resq)]
          [(== `(~ (// ,p ,q)) i) (== `(& (~ ,resp) (~ ,resq)) o) (cnfo p resp) (cnfo q resq)]
          [(== `(~ (& ,p ,q)) i) (== `(// (~ ,resp) (~ ,resq)) o) (cnfo p resp) (cnfo q resq)]
	  [(== `(// ,p (& ,q ,r)) i) (== `(& (// ,resp ,resq) (// ,resp ,resr)) o) (cnfo p resp) (cnfo q resq) (cnfo r resr)]
	  )))

(define (ground-termo? t)
  (fresh (p q)
	 (conde
	  [(simple-statement t)]
	  [(== `(~ ,p) t) (simple-statement p)]
	  [(== `(// ,p ,q) t) (simple-statement p) (simple-statement q)]
	  [(== `(& ,p ,q) t) (simple-statement p) (simple-statement q)]
	  )))

;(~ (~ (// a b))) => (// a b)
;(~ (~ (// a (// a (& b c))))) => (// a (// a (& b c)))
