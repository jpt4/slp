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

(define (nnfo i o)
  (fresh (a b)
         (conde
          [(== `(-> ,a ,b) i) (== `(// (~ ,a) ,b) o)])))
