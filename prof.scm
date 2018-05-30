;;prof.scm
;;20180401Z
;;jpt4
;;professorial propositional logic resolution algorithm
;;possibly also narrowing

(load "/home/jpt4/code/slp/miniKanren-with-symbolic-constraints/mk.scm")
(load "/home/jpt4/code/slp/miniKanren-with-symbolic-constraints/numbers.scm")
;;match.ss for dual rule generator
(load "/home/jpt4/code/slp/match.ss")

(define (any-statement s)
  (conde
   [(simple-statement s)]
   [(compound-statement s)]))

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//)])
  )

(define (compound-statement s)
  (fresh (sl sr)
         (conde
          [(noto sl c) (any-statement sl)]
          [(ando sl sr c) (any-statement sl) (any-statement sr)]
          [(oro sl sr c) (any-statement sl) (any-statement sr)]
          )))

;;compound statements
(define (noto s c) (== `(~ ,s) c))
(define (ando sl sr c) (== `(& ,sl ,sr) c))
(define (oro sl sr c) (== `(// ,sl ,sr) c))

(define (dneg i o)
  (fresh (x)
         (conde
          [(== `(~ (~ x)) i) (== x o)])))
(define (idem i o)
  (fresh (x)
         (conde
          [(== `(& ,x ,x) i) (== x o)])))
    (comm (& x y) (& y x))
    (assoc (& x (& y z)) (& (& x y) z))
    (absorp (& x (// x y)) x)
    (distr (& x (// y z)) (// (& x y) (& x z)))
    (dem (~ (& x y)) (// (~ x) (~ y)))
    (dichot (// x (~ x)) (// y (~ y)))))


          


