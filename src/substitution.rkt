#lang racket

(require (prefix-in u: "util.rkt")
         (prefix-in v: "variable.rkt"))

(provide 
  ext
  prefix 
  unify
  walk
  walk*
  (rename-out [empty-s empty]))

(define empty-s '())
(define (ext s k v) (cons `(,k . ,v) s))

(define (prefix s s^)
  (cond 
    [(null? s) s^]
    [else (let loop [(s s^)]
            (cond
              [(eq? s^ s) '()]
              [else (cons (car s^) (loop (cdr s^)))]))]))

(define (walk u s)
  (cond
    [(not (v:var? u)) u]
    [(assq u s) => (lambda [pr] (walk (u:rhs pr) s))]
    [else u])) 

(define (walk* w s)
  (let [(v (walk w s))]
    (cond
      [(v:var? v) v]
      [(pair? v)
       (cons (walk* (car v) s) 
             (walk* (cdr v) s))]
      [else v])))

(define (unify e s)
  (cond
    [(null? e) s]
    [else 
      (let loop [(u (caar e))
                 (v (cdar e))
                 (e (cdr e))]
        (let [(u (walk u s))
              (v (walk v s))]
          (cond
            [(eq? u v) (unify e s)]
            [(v:var? u)
             (and (not (occurs-check u v s))
                  (unify e (ext u v s)))]
            [(v:var? v)
             (and (not (occurs-check v u s))
                  (unify e (ext v u s)))]
            [(and (pair? u) (pair? v))
             (loop (car u) (car v)
                   `((,(cdr u) . ,(cdr v)) . ,e))]
            [(equal? u v) (unify e s)]
            [else #f])))]))

(define (occurs-check x v s)
  (let [(v (walk v s))]
    (cond
      [(v:var? v) (v:eq? v x)]
      [(pair? v)
       (or (occurs-check x (car v) s) 
           (occurs-check x (cdr v) s))]
      [else #f])))

