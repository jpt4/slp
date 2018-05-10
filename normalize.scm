;;normalize.scm
;;20180501Z
;;jpt4
;;Reduce arbitrary SL expression to clausal normal form

(load "miniKanren-with-symbolic-constraints/mk.scm")

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//) (=/= ss '->)]
   ))

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

(define (sentence s)
  (fresh (p q)
	 (conde
	  [(variable s)]
	  [(== `(~ ,p) s) (sentence p)]
	  [(== `(& ,p ,q) s) (sentence p) (sentence q)]
	  [(== `(// ,p ,q) s) (sentence p) (sentence q)]
	  [(== `(-> ,p ,q) s) (sentence p) (sentence q)]
)))

(define (impl-freeo i o)
  (fresh (p q resp resq)
	 ;(sentence p) (sentence q)
	 (conde
	  [(variable i) (== i o)]
	  [(== `(~ ,p) i) (sentence p) (impl-freeo p resp) (== `(~ ,resp) o)]
	  [(== `(& ,p ,q) i) (sentence p) (sentence q) (impl-freeo p resp) (impl-freeo q resq) (== `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (sentence p) (sentence q) (impl-freeo p resp) (impl-freeo q resq) (== `(// ,resp ,resq) o)]
	  [(== `(-> ,p ,q) i) (sentence p) (sentence q) (impl-freeo `(// (~ ,p) ,q) o)]
	  )))

(define (impl-freeo? s) (impl-freeo s s))

(define (nnfo i o)
  (fresh (p q resp resq respq)
	 (conde
	  [(variable i) (== i o)]
	  [(== `(~ (~ ,p)) i) (sentence p) (nnfo p o)]
	  [(== `(& ,p ,q) i) (sentence p) (sentence q) 
	   (nnfo p resp) (nnfo q resq) (== `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (sentence p) (sentence q) 
	   (nnfo p resp) (nnfo q resq) (== `(// ,resp ,resq) o)]
	  [(== `(~ (& ,p ,q)) i) (sentence p) (sentence q) 
	   (nnfo `(// (~ p) (~ )) o)]
	  [(== `(~ (// ,p ,q)) i) (sentence p) (sentence q) 
	   (nnfo `(& (~ p) (~ )) o)]
	  )))

(define (nnfo? s) (nnfo s s))
	   
(define (cnfo i o)
  (fresh (p q r carp carq resp resq resr respq respr resi)
         (conde
          [(cnfo? i) (== i o)]
          [(== `(// ,p (& ,q ,r)) i) 
           (cnfo `(// ,p ,q) respq) (cnfo `(// ,p ,r) respr)
           (cnfo `(& ,respq ,respr) o)]
          [(== `(// (& ,q ,r) ,p) i) 
           (cnfo `(// ,p (& ,q ,r)) o)]
          [(== `(// ,p ,q) i) (caro q carq) (=/= carq '&) 
           (cnfo `(// ,resp ,resq) o) 
           (cnfo p resp) (cnfo q resq)]
          [(== `(& ,p ,q) i) (== `(& ,resp ,resq) o) 
           (cnfo p resp) (cnfo q resq)]
          [(== `(~ (~ ,p)) i)  (cnfo p o)]
          [(== `(-> ,p ,q) i) (cnfo `(// (~ ,resp) ,resq) o) 
           (cnfo p resp) (cnfo q resq)]
          [(== `(~ (// ,p ,q)) i) (cnfo `(~ ,p) resp) (cnfo `(~ ,q) resq)
           (== `(& ,resp ,resq) o)]
          [(== `(~ (& ,p ,q)) i) (cnfo `(// (~ ,p) (~ ,q)) o)]
          )))

(define (caro i o)
  (fresh (a b)
         (== `(,a . ,b) i) (== a o)))

(define (ground-termo? t)
  (fresh (p q)
	 (conde
	  [(simple-statement t)]
	  [(== `(~ ,p) t) (simple-statement p)]
	  [(== `(// ,p ,q) t) (simple-statement p) (simple-statement q)]
	  [(== `(& ,p ,q) t) (simple-statement p) (simple-statement q)]
	  )))

;(~ (~ (// a b))) => (// a b)
#|(run 1 (q) (cnfo '(~ (~ (// a (// a (& b c)))))))
 => 
(// a (// a (& b c)))
(// a (& (// a b) (// a c)))
(& (// a (// a b)) (// a (// a c)))

> (load "normalize.scm")
> (run 1 (q) (cnfo '(~ (// a b)) q))
((& (~ a) (~ b)))
> (run 1 (q) (cnfo '(~ (// (~ a) (~ b))) q))
((& a b))
> (run 1 (q) (cnfo '(~ (// (~ (// a b)) (~ b))) q))
((& (// a b) b))
> (run 1 (q) (cnfo '(~ (// (// a b)) (~ b))) q))
Exception: incorrect number of arguments to #<procedure cnfo at normalize.scm:1033>
Type (debug) to enter the debugger.
> (run 1 (q) (cnfo '(~ (// (// a b) (~ b))) q))
((& (& (~ a) (~ b)) b))
> (run 1 (q) (cnfo '(// a (& b c)) q))
((& (// a b) (// a c)))
> (run 1 (q) (cnfo '(// a (// a (& b c))) q))


|#
