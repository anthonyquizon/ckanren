#lang racket

(require (prefix-in mk: "./miniKanren.rkt"))
(provide (all-defined-out))



(define empty-d '())
(define empty-c '())
(define empty-a (make-a mk:empty-s empty-d empty-c))
(define (ext-d d k v) (cons `(,k . ,v) d))

(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

(define make-a
  (lambda (s d c)
    (cons s (cons d c))))

(define-syntax lambdaM
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

(define identityM (lambda [a] a))

(define composeM
  (lambda [fm fm^]
    (lambda [a]
      (let [(a (fm a))]
        (and a (fm^ a))))))

(define (ext-c c k v)
  (lambda [oc c]
    (cond
      ((any/var? (oc->rands oc)) (cons oc c))
      (else c))))

(define (any/var? t)
  (cond
    [(mk:var? t) #t]
    [(pair? t)
     (or (any/var? (car t)) (any/var? (cdr t)))]
    [else #f]))

