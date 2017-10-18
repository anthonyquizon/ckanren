#lang racket

(provide (all-defined-out))

(define (var dummy) (vector dummy))
(define (var? x) (vector? x))
(define empty-s '())
(define (ext-s s k v) (cons `(,k . ,v) s))
(define (lhs pr) (car pr))
(define (rhs pr) (cdr pr))

(define-syntax lambdag
  (syntax-rules [:]
    ((_ (a : s d c r) body)
     (lambda [a]
       (let [(s (car a))
             (d (cadr a))
             (c (cddr a))]
         body)))
    ((_ (a) body) (lambda [a] body))))

(define unitg (lambdag [a] a))
(define mzerog (lambda [] #f))
(define choiceg (lambda [a f] (cons a f)))

