#lang racket

(require (prefix-in u: "./util.rkt"))

(provide 
  var
  var?
  any/var?
  any-relevant/var?
  recover/vars
  (rename-out [eq-var? eq?])
  ext/vars)

(define (var dummy) (vector dummy))
(define (var? x) (vector? x))
(define (eq-var? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (any/var? t)
  (cond
    [(var? t) #t]
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
      (let [(x (u:lhs (car p)))
            (v (u:rhs (car p)))
            (r (recover/vars (cdr p)))]
        (cond
          [(var? v) (ext/vars v (ext/vars x r))]
          [else (ext/vars x r)]))]))

(define (ext/vars x r)
  (cond
    [(memq x r) r]
    [else (cons x r)]))
