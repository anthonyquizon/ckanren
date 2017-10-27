#lang racket

(require 
  (prefix-in v: "variable.rkt")
  (prefix-in u: "util.rkt"))

(provide 
  copy-before
  drop-before
  (rename-out [make-dom make]
              [empty-d empty]
              [get-dom get]  
              [value?-dom value?]  
              [memv?-dom memv?]  
              [singleton?-dom singleton?]  
              [singleton-element-dom singleton-element]  
              [min-dom min]  
              [max-dom max]  
              [disjoint?-dom disjoint?]
              [diff-dom diff]
              [intersection-dom intersection]))

(define (make-dom n*) n*)
(define empty-d '())

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

(define (get-dom x d)
  (cond 
    [(assq x d) => u:rhs]
    [else #f]))

(define (value?-dom v) (and (integer? v) (<= 0 v)))
(define (memv?-dom v dom) (and (value?-dom v) (memv v dom)))
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

