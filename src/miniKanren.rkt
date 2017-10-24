#lang racket

(provide (all-defined-out))

(define (var dummy) (vector dummy))
(define (var? x) (vector? x))
(define (eq-var? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))
(define empty-s '())
(define (ext-s s k v) (cons `(,k . ,v) s))
(define (lhs pr) (car pr))
(define (rhs pr) (cdr pr))

(define (walk u s)
  (cond
    [(not (var? u)) u]
    [(assq u s) => (lambda [pr] (walk (rhs pr) s))]
    [else u])) 

(define (walk* w s)
  (let [(v (walk w s))]
    (cond
      [(var? v) v]
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
            [(var? u)
             (and (not (occurs-check u v s))
                  (unify e (ext-s u v s)))]
            [(var? v)
             (and (not (occurs-check v u s))
                  (unify e (ext-s v u s)))]
            [(and (pair? u) (pair? v))
             (loop (car u) (car v)
                   `((,(cdr u) . ,(cdr v)) . ,e))]
            [(equal? u v) (unify e s)]
            [else #f])))]))

(define (occurs-check x v s)
  (let [(v (walk v s))]
    (cond
      [(var? v) (eq-var? v x)]
      [(pair? v)
       (or (occurs-check x (car v) s) 
           (occurs-check x (cdr v) s))]
      [else #f])))

(define (reify-s v s)
  (let [(v (walk v s))]
    (cond
      [(var? v) (ext-s v (reify-n (size-s s)) s)]
      [(pair? v) (reify-s (cdr v) (reify-s (car v) s))]
      [else s])))

(define (reify-n n)
  (string->symbol
    (string-append "_" "." (number->string n)))) 

(define (size-s x)
  (length x))

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

;; NOTE: thunk
(define-syntax lambdaF
  (syntax-rules []
    [(_ [] e) (lambda [] e)]))

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

(define (take n f)
  (cond
    [(and n (zero? n)) '()]
    [else 
      (case-inf (f)
                [() '()]
                [(f) (take n f)]
                [(a) (cons a '())]
                [(a f) (cons a (take (and n (- n 1)) f))])]))

(define-syntax run
  (syntax-rules []
    [(_ n [x] g0 g ...)
     (take n
           (lambdaF []
                    ((fresh [x] g0 g ... (reify x))
                     empty-a)))]))

(define-syntax run*
  (syntax-rules []
    [(_ [x] g0 g ...) (run #f [x] g0 g ...)]))


;; Goal constructors
(define-syntax fresh
  (syntax-rules []
    [(_ (x ...) g0 g ...)
     (lambdaG [a]
              (inc
                (let [(x (var 'x)) ...]
                  (bindG* [g0 a] g ...))))]))

(define-syntax bindG*
  (syntax-rules []
    [(_ e) e]
    [(_ e g0 g ...) (bindG* (bindG e g0) g ...)]))

(define (bindG a-inf g)
  (case-inf a-inf
            [() (mzeroG)]
            [(f) (inc (bindG (f) g))]
            [(a) (g a)]
            [(a f) (mplusG (g a) (lambdaF [] (bindG (f) g)))]))

(define (mplusG a-inf f)
  (case-inf a-inf
            [() (f)]
            [(f^) (inc (mplusG (f) f^))]
            [(a) (choiceG a f)]
            [(a f^) (choiceG a (lambdaF [] (mplusG (f) f^)))])) 

(define-syntax conde
  (syntax-rules []
    [(_ (g0 g ...) (g1 g^ ...) ...)
     (lambdaG [a]
              (inc (mplusG* (bindG* (g0 a) g ...)
                            (bindG* (g1 a) g^ ...)
                            ...)))]))

(define-syntax mplusG*
  (syntax-rules []
    [(_ e) e]
    [(_ e0 e ...) (mplusG e0 (lambdaF [] (mplusG* e ...)))]))


;; Impure
(define-syntax condu
  (syntax-rules []
    [(_ (g0 g ...) (g1 g^ ...) ...) 
     (lambdaG [a] 
              (inc (if-u ((g0 a) g ...) ((g1 a) g^ ...) ...)))])) 

(define-syntax if-u
  (syntax-rules []
    [(_) (mzeroG)]
    [(_ (e g ...) b ...)
     (let loop [(a-inf e)]
       (case-inf a-inf
                 [() (if-u b ...)]
                 [(f) (inc (loop (f)))]
                 [(a) (bindG* a-inf g ...)]
                 [(a f) (bindG* a g ...)]))]))

(define (onceo g) (condu (g)))

