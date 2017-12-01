;;katz.scm
;;20171201Z
;;jpt4
;;study notes for Robert Katz, 1994,
;;"Classical Sentential Logic Based on Logical Equivalence",
;;using the slp.scm theorem prover as aid.
;;Chez Scheme v9.4.1+

(load "slp.scm")

;;Ch. 1
(define c1-eqvp 
  (case-lambda
   [(i)
    (run 1 (x y z) (== i x) (base-provero x y z))]
   [(n i) (number? n)
    (run n (x y z) (== i x) (base-provero x y z))]
   [(i o)
    (run 1 (x y z) (== i x) (== o z) (base-provero x y z))]
   [(n i o) (number? n)
    (run n (x y z) (== i x) (== o z) (base-provero x y z))]
   [(i t o)
    (run 1 (x y z) (== i x) (== t y) (== o z) (base-provero x y z))]
   [(n i t o) (number? n)
    (run n (x y z) (== i x) (== t y) (== o z) (base-provero x y z))]
))
