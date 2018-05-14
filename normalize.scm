;;normalize.scm
;;20180501Z
;;jpt4
;;Reduce arbitrary SL expression to clausal normal form

(load "miniKanren-with-symbolic-constraints/mk.scm")
(load "miniKanren-with-symbolic-constraints/numbers.scm")
(load "miniKanren-with-symbolic-constraints/test-check.scm")
(load "miniKanren-with-symbolic-constraints/test-interp.scm")

(define (add1o i o) (pluso i '(1) o))

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
	 (conde
	  [(impl-freeo? i) (== i o)]
	  [(== `(~ ,p) i) (sentence p) (impl-freeo p resp) (== `(~ ,resp) o)]
	  [(== `(& ,p ,q) i) (sentence p) (sentence q) 
     (impl-freeo p resp) (impl-freeo q resq) (== `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (sentence p) (sentence q) 
     (impl-freeo p resp) (impl-freeo q resq) (== `(// ,resp ,resq) o)]
	  [(== `(-> ,p ,q) i) (sentence p) (sentence q) 
     (impl-freeo `(// (~ ,p) ,q) o)]
	  )))

(define (impl-freeo? s) 
  (fresh (p q)
	 (conde
	  [(variable s)]
	  [(== `(~ ,p) s) (impl-freeo? p)]
	  [(== `(& ,p ,q) s) (impl-freeo? p) (impl-freeo? q)]
	  [(== `(// ,p ,q) s) (impl-freeo? p) (impl-freeo? q)]
	  )))

(define (nnfo i o)
  (fresh (p q p1 p2 resp resq respq)
	 (conde
    [(nnfo? i) (== i o)]
    [(== `(~ (~ ,p)) i) (impl-freeo? p) (nnfo p o)]
	  [(== `(& ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
	   (nnfo p resp) (nnfo q resq) (== `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
	   (nnfo p resp) (nnfo q resq) (== `(// ,resp ,resq) o)]
	  [(== `(~ (& ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
	   (nnfo `(// (~ ,p) (~ ,q)) o)]
	  [(== `(~ (// ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
	   (nnfo `(& (~ ,p) (~ ,q)) o)]
	  )))

(define (nnfo? s)
  (fresh (p q resp resq)
	 (conde
	  [(variable s)]
	  [(== `(~ ,p) s) (variable p)]
	  [(== `(& ,p ,q) s) (impl-freeo? p) (impl-freeo? q) 
     (nnfo? p) (nnfo? q)]
	  [(== `(// ,p ,q) s) (impl-freeo? p) (impl-freeo? q) 
     (nnfo? p) (nnfo? q)]
	  )))

(define (cnfo i o)
  (fresh (p q resp resq)
	 (conde
	  [(cnfo? i) (== i o)]
	  [(== `(& ,p ,q) i) (nnfo? i) (cnfo p resp) (cnfo q resq) 
	   (== `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (nnfo? i) (cnfo p resp) (cnfo q resq) 
     (distro `(// ,resp ,resq) o)]
	  )))

(define (distro i o)
  (cnfo? o)
  (fresh (s1 s2 p1 p2 q1 q2 resl resr)
	 (== `(// ,s1 ,s2) i)
	 (conde
	  [(cnfo? i) (== i o)]
	  [(== `(& ,p1 ,p2) s1) (cnfo? s1) (cnfo? s2)
     (distro `(// ,p1 ,s2) resl) (distro `(// ,p2 ,s2) resr) 
     (== `(& ,resl ,resr) o)]
	  [(== `(& ,q1 ,q2) s2) (=/= `(& ,p1 ,p2) s1)
	   (cnfo? s1) (cnfo? s2)
     (distro `(// ,s1 ,q1) resl) (distro `(// ,s1 ,q2) resr) 
     (== `(& ,resl ,resr) o)]
	  #;[(=/= `(& ,p1 ,p2) s1) (=/= `(& ,q1 ,q2) s2) 
	   (cnfo? s1) (cnfo? s2)
	   ;(== 'three o)]
	   (== `(// ,s1 ,s2) o)]
	  )))


(define (s->cnfo i o)
  (fresh (resi resn)
	 (impl-freeo i resi) (nnfo resi resn) (cnfo resn o)))

(define (thread-impl-freeo i o)
  (fresh (p q resp resq)
	 ;(sentence p) (sentence q)
	 (conde
	  [(impl-freeo? i) (thread-nnfo i o)]
	  ;[(variable i) (== i o)]
	  [(== `(~ ,p) i) (sentence p) (thread-impl-freeo p resp) 
     (thread-nnfo `(~ ,resp) o)]
	  [(== `(& ,p ,q) i) (sentence p) (sentence q) 
     (thread-impl-freeo p resp) (thread-impl-freeo q resq) 
     (thread-nnfo `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (sentence p) (sentence q) 
     (thread-impl-freeo p resp) (thread-impl-freeo q resq) 
     (thread-nnfo `(// ,resp ,resq) o)]
	  [(== `(-> ,p ,q) i) (sentence p) (sentence q) 
     (thread-impl-freeo `(// (~ ,p) ,q) o)]
	  )))

(define (thread-nnfo i o)
  (fresh (p q resp resq respq)
	 (conde
	  ;[(variable i) (== i o)]
	  ;[(== `(~ ,p) i) (variable p) (== i o)]
	  [(nnfo? i) (cnfo i o)]
	  [(== `(~ (~ ,p)) i) (impl-freeo? p) #;(sentence p) (thread-nnfo p o)]
	  [(== `(& ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
     ;(sentence p) (sentence q) 
	   (thread-nnfo p resp) (thread-nnfo q resq) (cnfo `(& ,resp ,resq) o)]
	  [(== `(// ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
     ;(sentence p) (sentence q) 
	   (thread-nnfo p resp) (thread-nnfo q resq) (cnfo `(// ,resp ,resq) o)]
	  [(== `(~ (& ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
     ;(sentence p) (sentence q) 
	   (thread-nnfo `(// (~ ,p) (~ ,q)) o)]
	  [(== `(~ (// ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
     ;(sentence p) (sentence q) 
	   (thread-nnfo `(& (~ ,p) (~ ,q)) o)]
	  )))

(define (diag-nnfo i o)
  (fresh (p q p1 p2 resp resq respq)
	 (conde
    [(nnfo? i) (== i o)]
	  #;[(== `(~ ,p) i) (== `(,p1 ,p2) p) (=/= '~ p1) 
     (impl-freeo? p) (diag-nnfo p resp) 
     ;(diag-nnfo`(~ ,resp) o)
     (== 'one o)]
	  [(== `(~ (~ ,p)) i) (impl-freeo? p) 
     (diag-nnfo p o)]
     ;(== 'two o)]
	  [(== `(& ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
     (diag-nnfo p resp) (diag-nnfo q resq) 
     (== `(& ,resp ,resq) o)]
     ;(== 'three o)]
	  [(== `(// ,p ,q) i) (impl-freeo? p) (impl-freeo? q) 
	   (diag-nnfo p resp) (diag-nnfo q resq) 
     (== `(// ,resp ,resq) o)]
    ;(== 'four o)]
	  [(== `(~ (& ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
	   (diag-nnfo`(// (~ ,p) (~ ,q)) o)]
    ;(== 'five o)]
	  [(== `(~ (// ,p ,q)) i) (impl-freeo? p) (impl-freeo? q) 
	   (diag-nnfo`(& (~ ,p) (~ ,q)) o)]
     ;(== 'six o)]
	  )))

#;(define (thread-s->cnfo i o)
  (fresh (resi)
         (conde
          [(se)])))
  

;;TODO eliminate duplicate results in s->cnfo and relation chain.

#;(define (old-cnfo i o)
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
#|(run 1 (q) (s->cnfo '(~ (~ (// a (// a (& b c))))) q))
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
