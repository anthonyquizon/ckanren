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
(define (make-dom n*) n*)
(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

;; NOTES:
  ;; oc = operator constraint
(define-syntax build-oc
  (syntax-rules []
    [(_ op arg ...)
     (build-aux-oc op (arg ...) () (arg ...))]))

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

(define (copy-before pred dom)
  (cond
    [(null? dom) '()]
    [(pred (car dom)) '()]
    [else (cons (car dom) (copy-before pred (cdr dom)))]))

(define (drop-before pred dom)
  (cond
    [(null? dom) '()]
    [(pred (car dom)) dom]
    [else (drop-before pred (cdr dom))]))

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

(define (get-dom x d)
  (cond 
    [(assq x d) => mk:rhs]
    [else #f]))

(define (value?-dom v) (and (integer? v) (<= 0 v)))
(define (memv?-dom v dom) (and (value?-deta v) (memv v dom)))
(define (null?-dom dom) (null? dom))
(define (singleton?-dom dom) (null? (cdr dom)))
(define (singleton-element-dom dom) (car dom))
(define (min-dom dom) (car dom))

(define (max-dom dom) 
  (cond 
    [(null? (cdr dom)) (car dom)]
    [else (max-dom (cdr dom))]))

(define (disjoint?-dom dom-1 dom-2)
  (cond
    [(or (null? dom-1) (null? dom-2)) #t]
    [(= (car dom-1) (car dom-2)) #f]
    [(< (car dom-1) (car dom-2))
     (disjoint?-dom (cdr dom-1) dom-2)]
    [else (disjoint?-dom dom-1 (cdr dom-2))]))

(define (diff-dom dom-1 dom-2)
  (cond
    [(or (null? dom-1) (null? dom-2)) dom-1]
    [(= (car dom-1) (car dom-2)) (diff-dom (cdr dom-1) (cdr dom-2))]
    [(< (car dom-1) (car dom-2))
     (cons (car dom-1) (diff-dom (cdr dom-1) dom-2))]
    [else (diff-dom dom-1 (cdr dom-2))]))

(define (intersection-dom dom-1 dom-2)
  (cond
    [(or (null? dom-1) (null? dom-2)) '()]
    [(= (car dom-1) (car dom-2))
     (cons (car dom-1)
           (intersection-dom (cdr dom-1) (cdr dom-2)))]
    [(< (car dom-1) (car dom-2))
     (intersection-dom (cdr dom-1) dom-2)]
    [else (intersection-dom dom-1 (cdr dom-2))]))

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
                   "Constrained variable ~s without dom"
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
                     [(get-dom x d)
                      => (lambda [dom]
                           ((composeM (process-dom v dom) t) a))]
                     [else (t a)]))))]))

(define (process-dom v dom)
  (lambdaM [a]
           (cond
             [(var? v) ((update-var-dom v dom) a)]
             [(memv?-dom v dom) a]
             [else #f])))

(define (update-var-dom x dom)
  (lambdaM [a : s d c]
           (cond
             [(get-dom x d)
              => (lambda [x-dom] 
                   (let [(i (intersection-dom x-dom dom))]
                     (cond
                       [(null?-dom i) #f]
                       [else ((resolve-sortable-dom i x) a)])))]
             [else ((resolve-sortable-dom dom x) a)])))

(define (resolve-sortable-dom dom x)
  (lambdaM [a : s d c]
           (cond
             [(singleton?-dom dom)
              (let* [(n (singleton-element-dom dom))
                     (a (make-a (ext-s x n s) d c))]
                ((run-constraints `(,x) c) a))]
             [else (make-a s (ext-d x dom d) c)])))

(define (enforce-constraints-fd x)
  (fresh []
    (force-ans x)
    (lambdaG [a : s d c]
             (let [(bound-x* (map lhs d))]
               (verify-all-bound c bound-x*)
               ((onceo (force-ans bound-x*)) a)))))

(define (force-ans x)
  (lambdaG [a : s d c]
           (let [(x (walk x s))]
             ((cond
                [(and (var? x) (get-dom x d))
                 => (map-sum (lambda [v] (== x v)))]
                [(pair? x)
                 (fresh []
                   (force-ans (car x))
                   (force-ans (cdr x)))]
                [else succeed]) 
              a))))

(define (reify-constraints-fd m r)
  (error 'reify-constraints "Unbound vars at end\n"))

(define (use-fd)
  (lambda ()
    (process-prefix process-prefix-fd)
    (enforce-constraints enforce-constraints-fd)
    (reify-constraints reify-constraints-fd)))

(define-syntax let-dom
  (syntax-rules [:]
    [(_ (s d) ((u : u-dom) ...) body)
     (let [(u (walk u s)) ...]
       (let [(u-dom (cond
                      [(var? u) (get-dom u d)]
                      [else (make-dom `(,u))]))
             ...]
         body))]))

(define-syntax c-op
  (syntax-rules [:]
    [(_ op ((u : u-dom) ...) body)
     (lambdaM [a : s d c]
              (let-dom [s d] [(u : u-dom) ...]
                       (let* [(c (ext-c (build-oc op u ...) c))
                              (a (make-a s d c))]
                         (cond
                           [(and u-dom ...) (body a)]
                           [else a]))))]))

(define (dom-fd x n*)
  (goal-construct (dom-c-fd x n*)))

(define (dom-c-fd x n*)
  (lambdaM [a : s d c]
           ((process-dom (walk x s) (make-dom n*)) a)))

(define (<=fd u v)
  (goal-construct (<=c-fd u v)))

(define (<=c-fd u v)
  (c-op <=c-fd [(u : u-dom) (v : v-dom)]
        (let [(u-min (min-dom u-dom))
              (v-max (max-dom v-dom))]
          (composeM
            (process-dom u
                         (copy-before (lambda [u] (< v-max u)) u-dom))
            (process-dom v
                         (drop-before (lambda [v] (<= u-min v)) v-dom))))))

(define (+fd u v w)
  (goal-construct (+c-fd u v w)))

(define (+c-fd u v w)
  (c-op +c-fd [(u : u-dom) (v : v-dom) (w : w-dom)]
        (let [(u-min (min-dom u-dom)) (u-max (max-dom u-dom))
              (v-min (min-dom u-dom)) (v-max (max-dom v-dom))
              (w-min (min-dom w-dom)) (w-max (max-dom w-dom))]
          (composeM
            (process-dom w
                         (range (+ u-min v-min) (+ u-max v-max)))
            (composeM 
              (process-dom u
                           (range
                             (- w-min v-max) (- w-max v-min)))
              (process-dom v
                           (range
                             (- w-min u-max) (- w-max u-min))))))))


(define (=/=fd u v)
  (goal-construct (=/=c-fd u v)))

(define (=/=c-fd u v)
  (lambdaM [a : s d c]
           (let-dom [s d] [(u : u-dom) (v : v-dom)]
                    (cond
                      [(or (not u-dom) (not v-dom))
                       (make-a s d (ext-c (build-oc =/=c-fd u v) c))]
                      [(and (singleton?-dom u-dom)
                            (singleton?-dom v-dom)
                            (= (singleton-element-dom u-dom)
                               (singleton-element-dom v-dom)))
                       #f]
                      [(disjoint?-dom u-dom v-dom) a]
                      [else 
                        (let* [(c^ (ext-c (build-oc =/=c-fd u v) c))
                               (a (make-a s d c^))]
                          (cond
                            [(singleton?-dom u-dom)
                             ((process-dom v (diff-dom v-dom u-dom)) a)]
                            [(singleton?-dom v-dom)
                             ((process-dom u (diff-dom u-dom v-dom)) a)]
                            [else a]))]))))


(define (all-diff-fd v*)
  (goal-construct (all-diff-c-fd v*)))

(define (all-diff-c-fd v*)
  (lambdaM [a : s d c]
           (let [(v* (walk v* s))]
             (cond
               [(var? v*)
                (let* [(oc (build-oc all-diff-c-fd v*))]
                  (make-a s d (ext-c oc c)))]
               [else 
                 (let-values [((x* n*) (partition var? v*))]
                   (let [(n* (list-sort < n*))]
                     (cond
                       [(list-sorted? < n*)
                        ((all-diff/c-fd x* n*) a)]
                       [else #f])))]))))


(define (all-diff/c-fd y* n*)
  (lambdaM [a : s d c]
           (let loop [(y* y*) (n* n*) (x* '())]
             (cond
               [(null? y*)
                (let* [(oc (build-oc all-diff/c-fd x* n*))
                       (a (make-a s d (ext-c oc c)))]
                  ((exclude-from-dom (make-dom n*) d x*) a))]
               [else 
                 (let [(y (walk (car y*) s))]
                   (cond
                     [(var? y) (loop (cdr y*) n* (cons y x*))]
                     [(memv?-dom y n*) #f]
                     [else (let [(n* (list-insert < y n*))]
                             (loop (cdr y*) n* x*))]))]))))

(define (exclude-from-dom dom-1 d x*)
  (let loop [(x* x*)]
    (cond
      [(null? x*) identityM]
      [(get-dom (car x*) d)
       => (lambda [dom-2]
            (composeM
              (process-dom (car x*) (diff-dom dom-2 dom-1))
              (loop (cdr x*))))]
      [else (loop (cdr x*))])))

