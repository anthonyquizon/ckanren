#lang racket

(require (prefix-in mk: "./miniKanren.rkt"))
(provide (all-defined-out))


(define process-prefix (make-parameter 'dummy))
(define enforce-constraints (make-parameter 'dummy))
(define reify-constraints (make-parameter 'dummy))
(define (make-a s d c) (cons s (cons d c)))
(define empty-d '())
(define empty-c '())
(define empty-a (make-a mk:empty-s empty-d empty-c))
(define (ext-d d k v) (cons `(,k . ,v) d))

(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

(define-syntax lambdam
  (syntax-rules [:]
    [(_ (a : s d c) body)
     (lambda [a]
       (let [(s (car a)) 
             (d (cadr a)) 
             (c (cddr a))]
         body))]
    [(_ [a] body) (lambda [a] body)]))

(define-syntax build-oc
  (syntax-rules ()
    [(_ op arg ...)
     (build-aux-oc op (arg ...) () (arg ...)) ]) )

(define-syntax build-aux-oc
  (syntax-rules ()
    [(_ op () (z ...) (arg ...))
     (let [(z arg) ...] 
       `(,(op z ...) . (op ,z ...)))]
    [(_ op (arg0 arg ...) (z ...) args)
     (build-aux-oc op (arg ...) (z ... q) args)])) 

(define (identityM a) a)

(define (composeM fm fm^)
    (lambda [a]
      (let [(a (fm a))]
        (and a (fm^ a)))))

(define (ext-c oc c)
  (cond
    ((any/var? (oc->rands oc)) (cons oc c))
    (else c)))

(define (any/var? t)
  (cond
    [(mk:var? t) #t]
    [(pair? t)
     (or (any/var? (car t)) (any/var? (cdr t)))]
    [else #f]))

(define (goal-construct fm)
  (mk:lambdag [a]
    (cond
      ((fm a) => mk:unitg)
      (else (mk:mzerog)))))

(define (== u v)
  (goal-construct (==c u v)))

(define (==c w v)
  (lambdam 
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



