#lang racket

(provide (all-defined-out))

(define (var dummy) (vector dummy))
(define (var? x) (vector? x))
(define empty-s '())
(define (ext-s s k v) (cons `(,k . ,v) s))
(define (lhs pr) (car pr))
(define (rhs pr) (cdr pr))

