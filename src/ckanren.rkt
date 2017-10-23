#lang racket

(require (prefix-in mk: "./miniKanren.rkt"))
(require (for-syntax (prefix-in mk: "./miniKanren.rkt")))
(provide (all-defined-out))

(define process-prefix (make-parameter 'dummy))
(define enforce-constraints (make-parameter 'dummy))
(define reify-constraints (make-parameter 'dummy))
(define (make-a s d c) (cons s (cons d c)))
(define empty-d '())
(define empty-c '())
(define empty-a (make-a mk:empty-s empty-d empty-c))
(define (ext-d d k v) (cons `(,k . ,v) d))
(define (make-domain n*) n*)
(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

;; NOTES:
  ;; oc = operator constraint
(define-syntax build-oc
  (syntax-rules []
    [(_ op arg ...)
     (build-aux-oc op (arg ...) () (arg ...)) ]) )

(define-syntax build-aux-oc
  (syntax-rules []
    [(_ op () (z ...) (arg ...))
     (let [(z arg) ...] 
       `(,(op z ...) . (op ,z ...)))]
    [(_ op (arg0 arg ...) (z ...) args)
     (build-aux-oc op (arg ...) (z ... q) args)])) 

(define (list-sorted? pred ls)
  (cond 
    [(or (null? ls) (null? (cdr ls))) #t]
    [(pred (car ls) (cadr ls)) (list-sorted? pred (cdr ls))]
    [else #f]))

(define (list-insert pred x ls)
  (cond 
    [(null? ls) (cons x '())]
    [(pred x (car ls)) (cons x ls)]
    [else (cons (car ls) (list-insert pred x (cdr ls)))]))

(define (copy-before pred domain)
  (cond
    [(null? domain) '()]
    [(pred (car domain)) '()]
    [else (cons (car domain) (copy-before pred (cdr domain)))]))

(define (drop-before pred domain)
  (cond
    [(null? domain) '()]
    [(pred (car domain)) domain]
    [else (drop-before pred (cdr domain))]))

(define (map-sum)
  (letrec 
    [(loop (lambda [ls] 
             (cond
               [(null? ls) fail]
               [else 
                 (mk:conde
                   [(f (car ls))]
                   [(loop (cdr ls))]) ])))]
    loop))

(define (get-domain x d)
  (cond 
    [(assq x d) => mk:rhs]
    [else #f]))

(define (value?-domain v) (and (integer? v) (<= 0 v)))
(define (memv?-domain v domain) (and (value?-deta v) (memv v domain)))
(define (null?-domain domain) (null? domain))
(define (singleton?-domain domain) (null? (cdr domain)))
(define (singleton-element-domain domain) (car domain))
(define (min-domain domain) (car domain))

(define (max-domain domain) 
  (cond 
    [(null? (cdr domain)) (car domain)]
    [else (max-domain (cdr domain))]))

(define (disjoint?-domain domain-1 domain-2)
  (cond
    [(or (null? domain-1) (null? domain-2)) #t]
    [(= (car domain-1) (car domain-2)) #f]
    [(< (car domain-1) (car domain-2))
     (disjoint?-domain (cdr domain-1) domain-2)]
    [else (disjoint?-domain domain-1 (cdr domain-2))]))

(define (diff-domain domain-1 domain-2)
  (cond
    [(or (null? domain-1) (null? domain-2)) domain-1]
    [(= (car domain-1) (car domain-2)) (diff-domain (cdr domain-1) (cdr domain-2))]
    [(< (car domain-1) (car domain-2))
     (cons (car domain-1) (diff-domain (cdr domain-1) domain-2))]
    [else (diff-domain domain-1 (cdr domain-2))]))

(define (intersection-domain domain-1 domain-2)
  (cond
    [(or (null? domain-1) (null? domain-2)) '()]
    [(= (car domain-1) (car domain-2))
     (cons (car domain-1)
           (intersection-domain (cdr domain-1) (cdr domain-2)))]
    [(< (car domain-1) (car domain-2))
     (intersection-domain (cdr domain-1) domain-2)]
    [else (intersection-domain domain-1 (cdr domain-2))]))

(define (any/var? t)
  (cond
    [(mk:var? t) #t]
    [(pair? t)
     (or (any/var? (car t)) (any/var? (cdr t)))]
    [else #f]))

(define (any-relevant/var? t x*)
  (cond
    [(var? t) (memq t x*)]
    [(pair? t) (or (any-relevant/var? (car t) x*)
                   (any-relevant/var? (cdr t) x*))]
    [else #f]))

(define (recover/vars p)
  (cond
    [(null? p) '()]
    [else 
      (let [(x (lhs (car p)))
            (v (rhs (car p)))
            (r (recover/vars (cdr p)))]
        (cond
          [(var? v) (ext/vars v (ext/vars x r))]
          [else (ext/vars x r)]))]))

(define (ext/vars x r)
  (cond
    [(memq x r) r]
    [else (cons x r)]))

(define (verify-all-bound c bound-x*)
  (unless (null? c)
    (cond
      [(find (lambda [x] (not (memq x bound-x*)))
             (filter var? (oc->rands (car c))))
       => (lambda [x]
            (error 'verify-all-bound
                   "Constrained variable ~s without domain"
                   x))]
      [else (verify-all-bound (cdr c) bound-x*)])))

(define (subsumes? p s)
  (cond
    [(mk:unify p s) => (lambda [s^] (eq? s s^))]
    [else #f]))

(define-syntax lambdaM
  (syntax-rules [:]
    [(_ (a : s d c) body)
     (lambda [a]
       (let [(s (car a)) 
             (d (cadr a)) 
             (c (cddr a))]
         body))]
    [(_ [a] body) (lambda [a] body)]))

(define (identityM a) a)

(define (composeM fM fM^)
    (lambda [a]
      (let [(a (fM a))]
        (and a (fM^ a)))))

(define (ext-c oc c)
  (cond
    [(any/var? (oc->rands oc)) (cons oc c)]
    [else c]))

(define (goal-construct fM)
  (mk:lambdaG [a]
    (cond
      [(fM a) => mk:unitG] ;;if fM returns a package -> create goal
      [else (mk:mzeroG)])))

(define (== u v)
  (goal-construct (==c u v)))

(define (==c w v)
  (lambdaM
    [a : s d c]
    (cond 
      [(mk:unify `((,u . ,v)) s) 
       => (lambda [s^]
            (cond
              [(eq? s s^) a]
              [else 
                (let [(p (prefix-s s s^))
                      (a (make-a s^ d c))]
                  (((process-prefix) p c) a))]))]
      [else #f])))

(define (prefix-s s s^)
  (cond 
    [(null? s) s^]
    [else (let loop [(s s^)]
            (cond
              [(eq? s^ s) '()]
              [else (cons (car s^) (loop (cdr s^)))]))]))

(define fail (== #f #t))
(define succeed (== #f #f))

(define (run-constraints x* c)
  (cond
    [(null? c) identityM]
    [(any-relevant/var? (oc->rands (car c)) x*)
     (composeM
       (rem/run (car c))
       (run-constraints x* (cdr c)))]
    [else (run-constraints x* (cdr c))]))

(define (rem/run oc)
  (lambdaM [a : s d c]
           (cond 
             [(memq oc c)
              (let [(c^ (remq oc c))]
                ((oc->proc oc) (make-a s d c^)))]
             [else a])))

(define (reify x)
  (fresh []
    ((enforce-constraints) x)
    (mk:lambdaG [a : s d c]
                (mk:choiceG
                  (let* [(v (mk:walk* x s))
                         (r (mk:reify-s v mk:empty-s))]
                    (cond
                      [(null? r) v]
                      [else 
                        (let [(v (mk:walk* v r))]
                          (cond
                            [(null? c) v]
                            [else 
                              (((reify-constraints) v r) a)]))]))
                  empty-f))))

(define (process-prefix-fd p c)
  (cond 
    [(null? p) identityM]
    [else
      (let [(x (lhs (car p)))
            (v (rhs (car p)))]
        (let [(t (composeM
                   (run-constraints `(,x) c)
                   (process-prefix-fd (cdr p) c)))]
          (lambdaM [a : s d c] 
                   (cond
                     [(get-domain x d)
                      => (lambda [domain]
                           ((composeM (process-domain v domain) t) a))]
                     [else (t a)]))))]))

(define (process-domain v domain)
  (lambdaM [a]
           (cond
             [(var? v) ((update-var-domain v domain) a)]
             [(memv?-domain v domain) a]
             [else #f])))

(define (update-var-domain x domain)
  (lambdaM [a : s d c]
           (cond
             [(get-domain x d)
              => (lambda [x-domain] 
                   (let [(i (intersection-domain x-domain domain))]
                     (cond
                       [(null?-domain i) #f]
                       [else ((resolve-sortable-domain i x) a)])))]
             [else ((resolve-sortable-domain domain x) a)])))

(define (resolve-sortable-domain domain x)
  (lambdaM [a : s d c]
           (cond
             [(singleton?-domain domain)
              (let* [(n (singleton-element-domain domain))
                     (a (make-a (ext-s x n s) d c))]
                ((run-constraints `(,x) c) a))]
             [else (make-a s (ext-d x domain d) c)])))

