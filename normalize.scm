;;normalize.scm
;;20180501Z
;;jpt4
;;Reduce arbitrary SL expression to disjunctive normal form

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//)])
  )

(define (variable s) (simple-statement s))

(define (diso? s)
  (fresh (c d)
         (conde
          [(== `(// ,c ,d) s) (conjo? c) (diso? d)]
          [(diso? s)])))

(define (conjo? s)
  (fresh (l c)
         (conde
          [(== `(& ,l ,c) s) (lito? l) (conjo? c)]
          [(lito? s)])))

(define (lito? s)
  (fresh (v)
         (conde
          [(== `(~ ,v) s) (variable v)]
          [(variable s)])))
  
