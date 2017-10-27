#lang racket

(require 
  (prefix-in pa: "parameter.rkt")
  (prefix-in p: "package.rkt")
  (prefix-in u: "util.rkt")
  (prefix-in d: "domain.rkt"))

(define (use-fd)
  (lambda ()
    (pa:process-prefix process-prefix-fd)
    (pa:enforce-constraints enforce-constraints-fd)
    (pa:reify-constraints reify-constraints-fd)))

(define (process-prefix-fd p c)
  (cond 
    [(null? p) p:identityM]
    [else
      (let [(x (u:lhs (car p)))
            (v (u:rhs (car p)))]
        (let [(t (p:composeM
                   (p:run-constraints `(,x) c)
                   (process-prefix-fd (cdr p) c)))]
          (p:lambdaM [a : s d c] 
                   (cond
                     [(d:get-dom x d)
                      => (lambda [dom]
                           ((p:composeM (c:process-dom v dom) t) a))]
                     [else (t a)]))))]))

(define (enforce-constraints-fd x)
  (m:fresh []
    (c:force-ans x)
    (m:lambdaG [a : s d c]
             (let [(bound-x* (map m:lhs d))]
               (c:verify-all-bound c bound-x*)
               ((m:onceo (c:force-ans bound-x*)) a)))))

(define (reify-constraints-fd m r)
  (error 'reify-constraints "Unbound vars at end\n"))

(define (dom-fd x n*)
  (c:goal-construct (dom-c-fd x n*)))

(define (dom-c-fd x n*)
  (c:lambdaM [a : s d c]
           ((c:process-dom (m:walk x s) (c:make-dom n*)) a)))

(define (<=fd u v)
  (c:goal-construct (<=c-fd u v)))

(define (<=c-fd u v)
  (c:c-op <=c-fd [(u : u-dom) (v : v-dom)]
        (let [(u-min (c:min-dom u-dom))
              (v-max (c:max-dom v-dom))]
          (p:composeM
            (c:process-dom u
                         (c:copy-before (lambda [u] (< v-max u)) u-dom))
            (c:process-dom v
                         (c:drop-before (lambda [v] (<= u-min v)) v-dom))))))

(define (+fd u v w)
  (c:goal-construct (+c-fd u v w)))

(define (+c-fd u v w)
  (c:c-op +c-fd [(u : u-dom) (v : v-dom) (w : w-dom)]
        (let [(u-min (c:min-dom u-dom)) (u-max (c:max-dom u-dom))
              (v-min (c:min-dom u-dom)) (v-max (c:max-dom v-dom))
              (w-min (c:min-dom w-dom)) (w-max (c:max-dom w-dom))]
          (p:composeM
            (c:process-dom w
                         (range (+ u-min v-min) (+ u-max v-max)))
            (p:composeM 
              (c:process-dom u
                           (range
                             (- w-min v-max) (- w-max v-min)))
              (c:process-dom v
                           (range
                             (- w-min u-max) (- w-max u-min))))))))

(define (=/=fd u v)
  (c:goal-construct (=/=c-fd u v)))

(define (=/=c-fd u v)
  (c:lambdaM [a : s d c]
           (c:let-dom [s d] [(u : u-dom) (v : v-dom)]
                    (cond
                      [(or (not u-dom) (not v-dom))
                       (c:make-a s d (c:ext-c (c:build-oc =/=c-fd u v) c))]
                      [(and (c:singleton?-dom u-dom)
                            (c:singleton?-dom v-dom)
                            (= (c:singleton-element-dom u-dom)
                               (c:singleton-element-dom v-dom)))
                       #f]
                      [(c:disjoint?-dom u-dom v-dom) a]
                      [else 
                        (let* [(c^ (c:ext-c (c:build-oc =/=c-fd u v) c))
                               (a (c:make-a s d c^))]
                          (cond
                            [(c:singleton?-dom u-dom)
                             ((c:process-dom v (c:diff-dom v-dom u-dom)) a)]
                            [(c:singleton?-dom v-dom)
                             ((c:process-dom u (c:diff-dom u-dom v-dom)) a)]
                            [else a]))]))))


(define (all-diff-fd v*)
  (c:goal-construct (all-diff-c-fd v*)))

(define (all-diff-c-fd v*)
  (c:lambdaM [a : s d c]
           (let [(v* (m:walk v* s))]
             (cond
               [(m:var? v*)
                (let* [(oc (c:build-oc all-diff-c-fd v*))]
                  (c:make-a s d (c:ext-c oc c)))]
               [else 
                 (let-values [((x* n*) (partition m:var? v*))]
                   (let [(n* (sort n* <))]
                     (cond
                       [(c:list-sorted? < n*)
                        ((all-diff/c-fd x* n*) a)]
                       [else #f])))]))))

(define (all-diff/c-fd y* n*)
  (c:lambdaM [a : s d c]
           (let loop [(y* y*) (n* n*) (x* '())]
             (cond
               [(null? y*)
                (let* [(oc (c:build-oc all-diff/c-fd x* n*))
                       (a (c:make-a s d (c:ext-c oc c)))]
                  ((exclude-from-dom (c:make-dom n*) d x*) a))]
               [else 
                 (let [(y (m:walk (car y*) s))]
                   (cond
                     [(m:var? y) (loop (cdr y*) n* (cons y x*))]
                     [(c:memv?-dom y n*) #f]
                     [else (let [(n* (c:list-insert < y n*))]
                             (loop (cdr y*) n* x*))]))]))))

(define (exclude-from-dom dom-1 d x*)
  (let loop [(x* x*)]
    (cond
      [(null? x*) c:identityM]
      [(d:get-dom (car x*) d)
       => (lambda [dom-2]
            (p:composeM
              (c:process-dom (car x*) (c:diff-dom dom-2 dom-1))
              (loop (cdr x*))))]
      [else (loop (cdr x*))])))


(define (force-ans x)
  (m:lambdaG [a : s d c]
           (let [(x (m:walk x s))]
             ((cond
                [(and (m:var? x) (get-dom x d))
                 => (map-sum (lambda [v] (== x v)))]
                [(pair? x)
                 (m:fresh []
                   (force-ans (car x))
                   (force-ans (cdr x)))]
                [else succeed]) 
              a))))

(define (map-sum f)
  (letrec 
    [(loop (lambda [ls] 
             (cond
               [(null? ls) fail]
               [else 
                 (m:conde
                   [(f (car ls))]
                   [(loop (cdr ls))])])))]
    loop))

(define (verify-all-bound c bound-x*)
  (unless (null? c)
    (cond
      [(findf (lambda [x] (not (memq x bound-x*)))
             (filter m:var? (oc->rands (car c))))
       => (lambda [x]
            (error 'verify-all-bound
                   "Constrained variable ~s without dom"
                   x))]
      [else (verify-all-bound (cdr c) bound-x*)])))

(define (process-dom v dom)
  (p:lambdaM [a]
           (cond
             [(v:var? v) ((update-var-dom v dom) a)]
             [(memv?-dom v dom) a]
             [else #f])))

(define (update-var-dom x dom)
  (p:lambdaM [a : s d c]
           (cond
             [(get-dom x d)
              => (lambda [x-dom] 
                   (let [(i (intersection-dom x-dom dom))]
                     (cond
                       [(null?-dom i) #f]
                       [else ((resolve-sortable-dom i x) a)])))]
             [else ((resolve-sortable-dom dom x) a)])))

(define (resolve-sortable-dom dom x)
  (p:lambdaM [a : s d c]
           (cond
             [(singleton?-dom dom)
              (let* [(n (singleton-element-dom dom))
                     (a (make-a (m:ext-s x n s) d c))]
                ((run-constraints `(,x) c) a))]
             [else (make-a s (ext-d x dom d) c)])))

(define-syntax let-dom
  (syntax-rules [:]
    [(_ (s d) ((u : u-dom) ...) body)
     (let [(u (m:walk u s)) ...]
       (let [(u-dom (cond
                      [(v:var? u) (get-dom u d)]
                      [else (make-dom `(,u))]))
             ...]
         body))]))

(define-syntax c-op
  (syntax-rules [:]
    [(_ op ((u : u-dom) ...) body)
     (p:lambdaM [a : s d c]
              (let-dom [s d] [(u : u-dom) ...]
                       (let* [(c (ext-c (build-oc op u ...) c))
                              (a (make-a s d c))]
                         (cond
                           [(and u-dom ...) (body a)]
                           [else a]))))]))

