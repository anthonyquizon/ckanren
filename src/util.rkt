#lang racket

(provide 
  lhs
  rhs
  list-insert
  list-sorted?)

(define (lhs pr) (car pr))
(define (rhs pr) (cdr pr))

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

