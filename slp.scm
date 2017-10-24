;; slp.scm
;; UTC20170909
;; jpt4
;; sentential logic prover, from Robert Katz, 1994,
;; "Classical Sentential Logic Based on Logical Equivalence"
;; Chez Scheme v9.4.1

(load "miniKanren-with-symbolic-constraints/mk.scm")
(load "miniKanren-with-symbolic-constraints/numbers.scm")
;;match.ss for dual rule generator
(load "match.ss")
n
(define (any-statement s)
  (conde
   [(simple-statement s)]
   [(compound-statement s)]))

(define (compound-statement c)
  (fresh (s1 s2)
         (conde
          [(mk-not s1 c) (any-statement s1)]
          [(mk-and s1 s2 c) (any-statement s1) (any-statement s2)]
          [(mk-or s1 s2 c) (any-statement s1) (any-statement s2)]
)))

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//)])
  )

(define (mk-not s c) (== `(~ ,s) c))
(define (mk-and s1 s2 c) (== `(& ,s1 ,s2) c))
(define (mk-or s1 s2 c) (== `(// ,s1 ,s2) c))

;;Characteristic, symmetric, and dual equivalence rule generation
;given a characteristic rule, produce a characteristic rule procedure
;ex. (~ (& a b)) (& (~ a) (~ b)) => 
#;(lambda (i o)
  (conde
   [(fresh (a b)
           (any-statement a) (any-statement b)
           (== `(~ (& ,a ,b)) i)
           (== `(& (~ ,a) (~ ,b)) o))]))

;;build rule as value
(define (build-named-rule n l r) (build-named-rule-value n l r))
(define (build-named-rule-value n l r)
  (let* ([rule-source (build-rule-value l r)]
         [sym-rule-source (build-sym-rule-value l r)]
         [dual-rule-source (build-dual-rule-value l r)]
         [sym-dual-rule-source (build-sym-dual-rule-value l r)])
    (define-top-level-value (rule-source-name n) rule-source)
    (define-top-level-value n (eval rule-source))
    (define-top-level-value (rule-source-name (sym-rule-name n))
      sym-rule-source)
    (define-top-level-value (sym-rule-name n) (eval sym-rule-source))
    (define-top-level-value (rule-source-name (dual-rule-name n))
      dual-rule-source)
    (define-top-level-value (dual-rule-name n) (eval dual-rule-source))
    (define-top-level-value (rule-source-name (sym-dual-rule-name n))
      sym-dual-rule-source)
    (define-top-level-value (sym-dual-rule-name n) (eval sym-dual-rule-source))
    ))

(define (build-rule-value l r) 
  (let* ([var-list (extract-vars (list l r))]
         [any-statements 
          (map (lambda (a)
                 (list 'any-statement a)) var-list)]
         [lhs (if (symbol? l)
                       (replace-sym-w-var-value l)
                       (list 'quasiquote (replace-sym-w-var-value l)))]
         [rhs (if (symbol? r)
                       (replace-sym-w-var-value r)
                       (list 'quasiquote (replace-sym-w-var-value r)))])
    (list 'lambda (list 'i 'o)
          (list 'fresh var-list
                  (list 'conde
                        (append any-statements
                                (list (list '== lhs 'i))
                                (list (list '== rhs 'o))))))))

(define (build-sym-rule-value l r)
  (build-rule-value r l))

(define (build-dual-rule-value l r)
  (dualize (build-rule-value l r)))

(define (build-sym-dual-rule-value l r)
  (build-dual-rule-value r l))

(define (replace-sym-w-var-value exp)
  (cond
   [(null? exp) exp]
   [(and (symbol? exp) (not (member exp connectives))) exp]
   [(member (car exp) connectives) 
    (cons (car exp) (replace-sym-w-var-value (cdr exp)))]
   [(pair? (car exp))
    (cons (replace-sym-w-var-value (car exp)) 
          (replace-sym-w-var-value (cdr exp)))]
   [(and (symbol? (car exp)) (not (member (car exp) connectives)))
    (cons (list 'unquote (car exp)) (replace-sym-w-var-value (cdr exp)))]))

;;auxiliaries
(define connectives '(~ & //))                       

(define (dualize exp)
  (map* swap-conj-disj exp))

(define (extract-vars exp) 
  (list-dedup 
   (filter (lambda (a) (not (member a connectives))) (list-flatten exp))))

(define (flat-list? ls)
  (andmap (lambda (a) (not (pair? a))) ls))

(define (list-count val ls)
  (let loop ([l ls] [acc 0])
    (let ([membval (member val l)])
      (if membval
        (loop (cdr membval) (+ 1 acc))
        acc))))

(define (list-dedup ls)
  (let aux ([l ls] [acc '()])
    (cond
     [(null? l) (reverse acc)]
     [(member (car l) acc) (aux (cdr l) acc)]
     [else (aux (cdr l) (cons (car l) acc))])))

(define (list-flatten ls)
  (cond
   [(null? ls) '()]
   [(not (list? ls)) ls]
   [(pair? (car ls)) (append (list-flatten (car ls))
                           (list-flatten (cdr ls)))]
   [else (cons (car ls) (list-flatten (cdr ls)))]))

(define (map* f ls)
  (cond
   [(null? ls) '()]
   [(pair? (car ls)) (cons (map* f (car ls)) (map* f (cdr ls)))]
   [else (cons (f (car ls)) (map* f (cdr ls)))]))

(define (swap-conj-disj sym)
  (case sym
   [& '//]
   [// '&]
   [else sym]))

;naming auxiliaries
(define (rule-source-name n)
  (string->symbol (string-append (symbol->string n) "-source")))
(define (sym-rule-name n)
  (string->symbol (string-append "sym-" (symbol->string n))))
(define (dual-rule-name n)
  (string->symbol (string-append "dual-" (symbol->string n))))
(define (sym-dual-rule-name n)
  (string->symbol (string-append "sym-" (symbol->string (dual-rule-name n)))))

;; Eight Assumed Equivalence Rules, Symmetries, Duals, and Symmetric Duals

;Double Negation
(build-named-rule 'dneg '(~ (~ x)) 'x)
;Idempotency
(build-named-rule 'idem '(& x x) 'x)
;Commutativity
(build-named-rule 'comm '(& x y) '(& y x))
;Associativity
(build-named-rule 'assoc '(& x (& y z)) '(& (& x y) z))
;Absorption
(build-named-rule 'absorp '(& x (// x y)) 'x)
;Distributivity
(build-named-rule 'distr '(& x (// y z)) '(// (& x y) (& x z)))
;DeMorgan's Rule
(build-named-rule 'dem '(~ (& x y)) '(// (~ x) (~ y)))
;Dichotomy
(build-named-rule 'dichot '(// x (~ x)) '(// y (~ y)))

;; Syntactically mark statements as equivalent.
(define (mk-eqv i o)
  (conde
   [(eqvo i o) `(eqv i o)]))

(define (eqvo i t o)
  (fresh (x y new-exp res-sub-t sub-t sub-o
            s1 s2 res-sub-t-1 res-sub-t-2 sub-t-1 sub-t-2 sub-o-1 sub-o-2)
         (conde
          ;trivial result
          [(== i o) (== '() t)]
          ;simple statement grounding
          [(simple-statement i) (== `((,i simp)) t) (== i o)]
          ;eight equivalence rules - contraction
          [(dneg i x) (== `((,x dneg) . ,y) t) 
           #;(rule-result-cycle-check x t) (eqvo x y o)]
          [(idem i x) (== `((,x idem) . ,y) t) (eqvo x y o)]
          [(comm i x) (== `((,x comm) . ,y) t) (eqvo x y o)]
          [(assoc i x) (== `((,x assoc) . ,y) t) (eqvo x y o)]
          [(absorp i x) (== `((,x absorp) . ,y) t) (eqvo x y o)]          
          [(distr i x) (== `((,x distr) . ,y) t) (eqvo x y o)]          
          [(dem i x) (== `((,x dem) . ,y) t) (eqvo x y o)]          
          [(dichot i x) (== `((,x dichot) . ,y) t) (eqvo x y o)]          
          ;eight symmetric equivalence rules - expansion
          [(sym-dneg i x) (== `((,x sym-sym-dneg) . ,y) t) (eqvo x y o)]
          [(sym-idem i x) (== `((,x sym-idem) . ,y) t) (eqvo x y o)]
          [(sym-comm i x) (== `((,x sym-comm) . ,y) t) (eqvo x y o)]
          [(sym-assoc i x) (== `((,x sym-assoc) . ,y) t) (eqvo x y o)]
          [(sym-absorp i x) (== `((,x sym-absorp) . ,y) t) (eqvo x y o)]
          [(sym-distr i x) (== `((,x sym-distr) . ,y) t) (eqvo x y o)]          
          [(sym-dem i x) (== `((,x sym-dem) . ,y) t) (eqvo x y o)]          
          [(sym-dichot i x) (== `((,x sym-dichot) . ,y) t) (eqvo x y o)]
          ;Substitution Principle - compound decomposition
          [(mk-not x i) (== `((,x not-comp) . ,res-sub-t) sub-t) 
           (eqvo x res-sub-t sub-o)
           (== `((sub-trace ,sub-t) . ,y) t)
           (== `(~ ,sub-o) new-exp)
           (eqvo new-exp y o)]
          [(mk-and s1 s2 i) 
           (== `((,s1 and-comp-1) . ,res-sub-t-1) sub-t-1) 
           (== `((,s2 and-comp-2) . ,res-sub-t-2) sub-t-2)            
           (eqvo s1 res-sub-t-1 sub-o-1)
           (eqvo s2 res-sub-t-2 sub-o-2)
           (== `((sub-trace ,sub-t-1) (sub-trace ,sub-t-2) . ,y) t)
           (== `(& ,sub-o-1 ,sub-o-2) new-exp)
           (eqvo new-exp y o)]
          [(mk-or s1 s2 i) 
           (== `((,s1 or-comp-1) . ,res-sub-t-1) sub-t-1) 
           (== `((,s2 or-comp-2) . ,res-sub-t-2) sub-t-2)            
           (eqvo s1 res-sub-t-1 sub-o-1)
           (eqvo s2 res-sub-t-2 sub-o-2)
           (== `((sub-trace ,sub-t-1) (sub-trace ,sub-t-2) . ,y) t)
           (== `(// ,sub-o-1 ,sub-o-2) new-exp)
           (eqvo new-exp y o)]
          )))

;; miniKanren auxiliaries
(define (mapo rel ls o)
  (fresh (a d res acc)
         (conde
          [(== '() ls) (== '() o)]
          [(== `(,a . ,d) ls) (rel a res) 
           (== `(,res . ,acc) o)
           (mapo rel d acc)]
          )))

(define (thunko i o)
  (== (lambda () i) o))

;;build-prover
;;generate miniKanren sl prover with a given corpus of rules
;;example rule: '(name lhs rhs), '(dem (~ (& a b)) (// (~ a) (~ b)))
#|(define (build-prover rls)
  (for-each (lambda (a) (build-named-rule (car a) (cadr a) (caddr a))) rls)
  (let ([root-names (map car rls)]
        [rule-names (list-flatten
                     (map (lambda (a) (list a 
                                            (sym-rule-name a) 
                                            (dual-rule-name a) 
                                            (sym-dual-rule-name a))) 
                          root-names))]
        [rules (map 
                (lambda (a) 
                  (list 
                   (list a 'i 'x) 
                   (list '== 'quasiquote 
                         (cons (list 'unquote 'x a) . 'unquote 'y) 't) 
                   (list 'prover-name 'x 'y 'o))) 
                rule-names)])
    (list 'lambda '(i t o) 
          (list 'fresh var-list
                (list 'conde
                      rules
  |#

;a fold is in order
(define (build-exp-as-list exp)
  (let ([exp->ls (lambda (e acc)
                   (cond
                    [(null? e) acc]
                    [(]
                    

#|
;rule r does not need to be passed quoted. (sym dneg 'x q) => (~ (~ x))
(define (sym r i o) 
  (r o i))
|#

#|
;;build rule as syntax
(define-syntax build-named-rule-syntax
  (syntax-rules ()
    [(_ n l r)
       (define-top-level-value n (eval (build-rule-syntax l r)))
       ]))

(define-syntax build-rule-syntax
  (syntax-rules ()
      [(_ l r)
       (let* ([var-list (extract-vars (list l r))]
              [any-statements (map (lambda (a)
                                     (syntax->datum #`(any-statement #,a)))
                                     var-list)]
              [lhs (if (symbol? l)
                       (replace-sym-w-var-syntax l)
                       (syntax->datum #``#,(replace-sym-w-var-syntax l)))]
              [rhs (if (symbol? r)
                       (replace-sym-w-var-syntax r)
                       (syntax->datum #``#,(replace-sym-w-var-syntax r)))]
              )
         `(lambda (i o) 
            (conde
             [,(append `(fresh ,var-list)
                       any-statements
                       `((== ,lhs i))
                       `((== ,rhs o))
                       )]))
         )]))

(define (build-sym-rule-syntax l r)
  (build-rule-syntax l r))

(define (build-dual-rule-syntax l r)
  (dualize (build-rule-syntax r l)))

(define (build-sym-dual-rule-syntax l r)
  (build-dual-rule-syntax r l))

(define (replace-sym-w-var-syntax exp)
  (cond
   [(null? exp) exp]
   [(and (symbol? exp) (not (member exp connectives))) exp]
   [(member (car exp) connectives) (cons (car exp) 
                                         (replace-sym-w-var-syntax (cdr exp)))]
   [(pair? (car exp))
    (cons (replace-sym-w-var-syntax (car exp)) 
          (replace-sym-w-var-syntax (cdr exp)))]
   [(let ([cexp (car exp)])
      (and (symbol? cexp) (not (member cexp connectives))) 
      (cons (syntax->datum #`,#,cexp) 
            (replace-sym-w-var-syntax (cdr exp))))]))
|#

