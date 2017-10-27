#lang racket

(provide 
  inc
  lambdaF
  empty-f
  case-inf
  take-f
  lambdaG
  unitG
  mzeroG
  choiceG)

(define-syntax lambdaF
  (syntax-rules []
    [(_ [] e) (lambda [] e)]))

;; incomplete stream
(define-syntax inc 
  (syntax-rules []
    [(_ e) (lambdaF [] e)]))

(define empty-f (lambdaF [] (mzeroG)))

(define-syntax case-inf
  (syntax-rules []
    [(_ e [() e0] ((f^) e1) ((a^) e2) ((a f) e3))
     (let [(a-inf e)]
       (cond
         [(not a-inf) e0]
         [(procedure? a-inf) (let [(f^ a-inf)] e1)]
         [(not (and (pair? a-inf)
                    (procedure? (cdr a-inf))))
          (let [(a^ a-inf)] e2)]
         [else (let [(a (car a-inf))
                     (f (cdr a-inf))]
                 e3)]))]))

(define (take-f n f)
  (cond
    [(and n (zero? n)) '()]
    [else 
      (case-inf (f)
                [() '()]
                [(f) (take-f n f)]
                [(a) (cons a '())]
                [(a f) (cons a (take-f (and n (- n 1)) f))])]))

(define-syntax lambdaG
  (syntax-rules [:]
    ((_ (a : s d c) body)
     (lambda [a]
       (let [(s (car a))
             (d (cadr a))
             (c (cddr a))]
         body)))
    ((_ (a) body) (lambda [a] body))))


(define unitG (lambdaG [a] a))
(define mzeroG (lambda [] #f))
(define choiceG (lambda [a f] (cons a f)))

