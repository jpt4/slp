;;katz.scm
;;20171201Z
;;jpt4
;;study notes for Robert Katz, 1994,
;;"Classical Sentential Logic Based on Logical Equivalence",
;;using the slp.scm theorem prover as aid.
;;Chez Scheme v9.4.1+

(load "/home/jpt4/code/slp/slp.scm")

;;Ch. 1
(define ch1-rule-defs
  '((dneg (~ (~ x)) x)
    (idem (& x x) x)
    (comm (& x y) (& y x))
    (assoc (& x (& y z)) (& (& x y) z))
    (absorp (& x (// x y)) x)
    (distr (& x (// y z)) (// (& x y) (& x z)))
    (dem (~ (& x y)) (// (~ x) (~ y)))
    (dichot (// x (~ x)) (// y (~ y)))))

(define ch1-rule-corpus (build-rule-corpus ch1-rule-defs '()))

;;ch1 prover
(build-named-prover 'ch1-provero ch1-rule-corpus)

;;chapter common auxiliaries
(define eqv
  (case-lambda
   [(p i)
    (run 1 (x y z) (== i x) (p x y z))]
   [(p n i) (number? n)
    (run n (x y z) (== i x) (p x y z))]
   [(p i o)
    (run 1 (x y z) (== i x) (== o z) (p x y z))]
   [(p n i o) (number? n)
    (run n (x y z) (== i x) (== o z) (p x y z))]
   [(p i t o)
    (run 1 (x y z) (== i x) (== t y) (== o z) (p x y z))]
   [(p n i t o) (number? n)
    (run n (x y z) (== i x) (== t y) (== o z) (p x y z))]
))
