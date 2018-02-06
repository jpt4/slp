
;; slp.scm
;; UTC20170909
;; jpt4
;; sentential logic prover, from Robert Katz, 1994,
;; "Classical Sentential Logic Based on Logical Equivalence"
;; Chez Scheme v9.4.1+

(load "/home/jpt4/code/slp/miniKanren-with-symbolic-constraints/mk.scm")
(load "/home/jpt4/code/slp/miniKanren-with-symbolic-constraints/numbers.scm")
;;match.ss for dual rule generator
(load "/home/jpt4/code/slp/match.ss")

(define (any-statement s)
  (conde
   [(simple-statement s)]
   [(compound-statement s)]))

(define (compound-statement c)
  (fresh (sl sr)
         (conde
          [(mk-not sl c) (any-statement sl)]
          [(mk-and sl sr c) (any-statement sl) (any-statement sr)]
          [(mk-or sl sr c) (any-statement sl) (any-statement sr)]
)))

(define (simple-statement ss)
  (conde
   [(symbolo ss) (=/= ss '~) (=/= ss '&) (=/= ss '//)])
  )

;;compound statements
(define (mk-not s c) (== `(~ ,s) c))
(define (mk-and sl sr c) (== `(& ,sl ,sr) c))
(define (mk-or sl sr c) (== `(// ,sl ,sr) c))

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

;;naming auxiliaries
(define (rule-source-name n)
  (string->symbol (string-append (symbol->string n) "-source")))
(define (sym-rule-name n)
  (string->symbol (string-append "sym-" (symbol->string n))))
(define (dual-rule-name n)
  (string->symbol (string-append "dual-" (symbol->string n))))
(define (sym-dual-rule-name n)
  (string->symbol (string-append "sym-" (symbol->string (dual-rule-name n)))))

;;Eight Assumed Equivalence Rules, Symmetries, Duals, and Symmetric Duals
(define base-rule-defs
  '((dneg (~ (~ x)) x)
    (idem (& x x) x)
    (comm (& x y) (& y x))
    (assoc (& x (& y z)) (& (& x y) z))
    (absorp (& x (// x y)) x)
    (distr (& x (// y z)) (// (& x y) (& x z)))
    (dem (~ (& x y)) (// (~ x) (~ y)))
    (dichot (// x (~ x)) (// y (~ y)))))

;;example rule: '(name lhs rhs), '(dem (~ (& a b)) (// (~ a) (~ b)))
(define build-rule-corpus 
  (case-lambda
   [(name-redex-pair-ls)
    (build-rule-corpus name-redex-pair-ls '(sym dual sym-dual))]
   [(name-redex-pair-ls flag-ls)
    (fold-right (lambda (a acc)
                  (let* ([name (car a)]
                         [lhs (cadr a)]
                         [rhs (caddr a)])
                    (build-named-rule name lhs rhs)
                    (remove (void)
                            (cons* name 
                                   (if (member 'sym flag-ls)
                                       (sym-rule-name name))
                                   (if (member 'dual flag-ls)
                                       (dual-rule-name name))
                                   (if (member 'sym-dual flag-ls)
                                       (sym-dual-rule-name name))
                                   acc))))
                '()
                name-redex-pair-ls)]))

(define base-rules
  (build-rule-corpus base-rule-defs))

;;build-prover
;;generate miniKanren sl prover with a given corpus of rules
(define (build-named-prover prover-name rule-name-ls)
  (let* 
      ([pn prover-name]
       [rule-clauses 
        (map (lambda (a) 
               (list (list a 'i 'x) 
                     (list '== (list 'quasiquote 
                                     (cons (list (list 'unquote 'x) a) 
                                           (list 'unquote 'y))) 't)
                     `(,pn x y o)))
             rule-name-ls)]
       [prover-source
        `(lambda (i t o)
           (fresh 
            (x y 
               new-exp res-sub-t sub-t sub-o
               sl sr res-sub-t-l res-sub-t-r sub-t-l sub-t-r sub-o-l sub-o-r)
            ,(append (list 'conde)
                     '([(== i o) (== '(end) t)])
                     '([(simple-statement i) (== `((,i simp)) t) (== i o)])
                     ;((sub-trace (((& a a) not-comp) (a idem))))
                     `([(mk-not x i) 
                       (== `((,x not-comp) . ,res-sub-t) sub-t) 
                       (,pn x res-sub-t sub-o)
                       (== `((sub-trace ,sub-t) . ,y) t)
                       (== `(~ ,sub-o) new-exp)
                       (,pn new-exp y o)])
                     `([(mk-and sl sr i)
                        (== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l) 
                        (== `((,sr and-comp-r) . ,res-sub-t-r) sub-t-r)
                        (,pn sl res-sub-t-l sub-o-l)
                        (,pn sr res-sub-t-r sub-o-r)
                        (== `((sub-trace ,sub-t-l) 
                              (sub-trace ,sub-t-r) . ,y) t)
                        (== `(& ,sub-o-l ,sub-o-r) new-exp)
                        (,pn new-exp y o)])
                     `([(mk-or sl sr i) 
                        (== `((,sl or-comp-l) . ,res-sub-t-l) sub-t-l) 
                        (== `((,sr or-comp-r) . ,res-sub-t-r) sub-t-r)        
                        (,pn sl res-sub-t-l sub-o-l)
                        (,pn sr res-sub-t-r sub-o-r)
                        (== `((sub-trace ,sub-t-l) 
                              (sub-trace ,sub-t-r) . ,y) t)
                        (== `(// ,sub-o-l ,sub-o-r) new-exp)
                        (,pn new-exp y o)])
                     rule-clauses)))])
    (define-top-level-value (rule-source-name pn) prover-source)
    (define-top-level-value pn (eval prover-source))))

;;base-provero
(build-named-prover 'base-provero base-rules)

;;Syntactically mark statements as equivalent.
(define (mk-eqv i o)
  (conde
   [(eqvo i o) `(eqv i o)]))

;;miniKanren auxiliaries
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

#|
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
|#

#|
(define (eqvo i t o)
  (fresh (x y new-exp res-sub-t sub-t sub-o
            sl sr res-sub-t-l res-sub-t-r sub-t-l sub-t-r sub-o-l sub-o-r)
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
          [(mk-and sl sr i) 
           (== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l) 
           (== `((,sr and-comp-r) . ,res-sub-t-r) sub-t-r)            
           (eqvo sl res-sub-t-l sub-o-l)
           (eqvo sr res-sub-t-r sub-o-r)
           (== `((sub-trace ,sub-t-l) (sub-trace ,sub-t-r) . ,y) t)
           (== `(& ,sub-o-l ,sub-o-r) new-exp)
           (eqvo new-exp y o)]
          [(mk-or sl sr i) 
           (== `((,sl or-comp-l) . ,res-sub-t-l) sub-t-l) 
           (== `((,sr or-comp-r) . ,res-sub-t-r) sub-t-r)            
           (eqvo sl res-sub-t-l sub-o-l)
           (eqvo sr res-sub-t-r sub-o-r)
           (== `((sub-trace ,sub-t-l) (sub-trace ,sub-t-r) . ,y) t)
           (== `(// ,sub-o-l ,sub-o-r) new-exp)
           (eqvo new-exp y o)]
          )))
|#

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

#|
notes and lessons
> (list (quote quasiquote) 'a)
`a
> (list 'quasiquote 'a)
`a

' =/= quote
' = (quote <the-operand>)

true desire
>'(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l) 
(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l) 
<however, I thought>
>`(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l) 
Exception: variable sl is not bound
Type (debug) to enter the debugger.
<similar to the result of>
>(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l)
Exception: variable sl is not bound
Type (debug) to enter the debugger.
<except it doesn't>
>`(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l)
(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l)
<regardless, the following tierce is also the case>
> (equal? `,(list '== (list 'quasiquote (cons (list (list 'unquote 'sl) 'and-comp-l) (list 'unquote 'res-sub-t-l))) 'sub-t-l) 
	  `(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l))
#t
> (eq? `,(list '== (list 'quasiquote (cons (list (list 'unquote 'sl) 'and-comp-l) (list 'unquote 'res-sub-t-l))) 'sub-t-l) 
       `(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l))
#f
> (eqv? `,(list '== (list 'quasiquote (cons (list (list 'unquote 'sl) 'and-comp-l) (list 'unquote 'res-sub-t-l))) 'sub-t-l) 
	'(== `((,sl and-comp-l) . ,res-sub-t-l) sub-t-l))
#f
<because (equal? '(a) (list 'a)) is #t.>
|#
