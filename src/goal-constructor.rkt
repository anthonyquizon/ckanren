#lang racket

(require 
  (prefix-in P: "parameter.rkt")
  (prefix-in i: "infs.rkt")
  (prefix-in p: "package.rkt")
  (prefix-in s: "substitution.rkt")
  (prefix-in v:  "variable.rkt")) 

(provide 
  ==
  conde
  fail
  succeed
  fresh)

(define (goal-construct fM)
  (i:lambdaG [a]
    (cond
      [(fM a) => i:unitG] ;;if fM returns a package -> create goal
      [else (i:mzeroG)])))

(define (== u v)
  (goal-construct (==c u v)))

(define (==c u v)
  (p:lambdaM
    [a : s d c]
    (cond 
      [(s:unify `((,u . ,v)) s) 
       => (lambda [s^]
            (cond
              [(eq? s s^) a]
              [else 
                (let [(p (s:prefix s s^))
                      (a (p:make s^ d c))]
                  (((P:process-prefix) p c) a))]))]
      [else #f])))

(define fail (== #f #t))
(define succeed (== #f #f))

;; Goal constructors
(define-syntax fresh
  (syntax-rules []
    [(_ (x ...) g0 g ...)
     (i:lambdaG [a]
              (i:inc
                (let [(x (v:var 'x)) ...]
                  (bindG* [g0 a] g ...))))]))

(define-syntax bindG*
  (syntax-rules []
    [(_ e) e]
    [(_ e g0 g ...) (bindG* (bindG e g0) g ...)]))

(define (bindG a-inf g)
  (i:case-inf a-inf
            [() (i:mzeroG)]
            [(f) (i:inc (bindG (f) g))]
            [(a) (g a)]
            [(a f) (mplusG (g a) (i:lambdaF [] (bindG (f) g)))]))

(define (mplusG a-inf f)
  (i:case-inf a-inf
            [() (f)]
            [(f^) (i:inc (mplusG (f) f^))]
            [(a) (i:choiceG a f)]
            [(a f^) (i:choiceG a (i:lambdaF [] (mplusG (f) f^)))])) 

(define-syntax conde
  (syntax-rules []
    [(_ (g0 g ...) (g1 g^ ...) ...)
     (i:lambdaG [a]
              (inc (mplusG* (bindG* (g0 a) g ...)
                            (bindG* (g1 a) g^ ...)
                            ...)))]))

(define-syntax mplusG*
  (syntax-rules []
    [(_ e) e]
    [(_ e0 e ...) (mplusG e0 (i:lambdaF [] (mplusG* e ...)))]))


;; Impure
(define-syntax condu
  (syntax-rules []
    [(_ (g0 g ...) (g1 g^ ...) ...) 
     (i:lambdaG [a] 
              (i:inc (if-u ((g0 a) g ...) ((g1 a) g^ ...) ...)))])) 

(define-syntax if-u
  (syntax-rules []
    [(_) (i:mzeroG)]
    [(_ (e g ...) b ...)
     (let loop [(a-inf e)]
       (i:case-inf a-inf
                 [() (if-u b ...)]
                 [(f) (i:inc (loop (f)))]
                 [(a) (bindG* a-inf g ...)]
                 [(a f) (bindG* a g ...)]))]))

(define (onceo g) (condu (g)))

