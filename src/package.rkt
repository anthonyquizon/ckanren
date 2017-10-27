#lang racket

(require (prefix-in s: "./substitution.rkt"))
(require (prefix-in d: "./domain.rkt"))
(require (prefix-in c: "./constraint.rkt"))

(provide 
  lambdaM
  identityM
  composeM 
  (rename-out [make-a make])
  (rename-out [empty-a empty]))

(define (make-a s d c) (cons s (cons d c)))
(define empty-a (make-a s:empty d:empty c:empty))

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
