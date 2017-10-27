#lang racket

(require 
  (prefix-in P:  "parameter.rkt")
  (prefix-in g: "goal-constructor.rkt")
  (prefix-in c:  "constraint.rkt")
  (prefix-in s:  "substitution.rkt")
  (prefix-in i:  "infs.rkt")
  (prefix-in p:  "package.rkt")
  (prefix-in v:  "variable.rkt"))

(provide run
         run*
         )

(define-syntax run
  (syntax-rules []
    [(_ n [x] g0 g ...)
     (i:take-f n
           (i:lambdaF []
                      ((g:fresh [x] g0 g ... (reify x))
                       p:empty)))]))

(define-syntax run*
  (syntax-rules []
    [(_ [x] g0 g ...) (run #f [x] g0 g ...)]))

(define (reify x)
  (g:fresh []
    ((P:enforce-constraints) x)
    (i:lambdaG [a : s d c]
                (i:choiceG
                  (let* [(v (s:walk* x s))
                         (r (reify-s v s:empty))]
                    (cond
                      [(null? r) v]
                      [else 
                        (let [(v (s:walk* v r))]
                          (cond
                            [(null? c) v]
                            [else 
                              (((P:reify-constraints) v r) a)]))]))
                  i:empty-f))))

(define (reify-s v s)
  (let [(v (s:walk v s))]
    (cond
      [(v:var? v) (s:ext v (reify-n (size-s s)) s)]
      [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
      [else s])))

(define (reify-n n)
  (string->symbol
    (string-append "_" "." (number->string n)))) 

(define (size-s x)
  (length x))
(define (run-constraints x* c)
  (cond
    [(null? c) p:identityM]
    [(v:any-relevant/var? (c:oc->rands (car c)) x*)
     (p:composeM
       (rem/run (car c))
       (run-constraints x* (cdr c)))]
    [else (run-constraints x* (cdr c))]))

(define (rem/run oc)
  (p:lambdaM [a : s d c]
           (cond 
             [(memq oc c)
              (let [(c^ (remq oc c))]
                ((c:oc->proc oc) (p:make s d c^)))]
             [else a])))

