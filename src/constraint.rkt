#lang racket

(require 
  (prefix-in v: "./variable.rkt"))

(provide 
  oc->proc
  oc->rator 
  oc->rands 
  oc->prefix
  build-oc
  (rename-out [empty-c empty]))

;; NOTE oc = operator constraint
(define empty-c '())

(define (oc->proc oc) (car oc))
(define (oc->rator oc) (car (cdr oc)))
(define (oc->rands oc) (cdr (cdr oc)))
(define (oc->prefix oc) (car (oc->rands oc)))

(define-syntax build-oc
  (syntax-rules []
    [(_ op arg ...)
     (build-aux-oc op (arg ...) () (arg ...))]))

(define-syntax build-aux-oc
  (syntax-rules []
    [(_ op () (z ...) (arg ...))
     (let [(z arg) ...] 
       `(,(op z ...) . (op ,z ...)))]
    [(_ op (arg0 arg ...) (z ...) args)
     (build-aux-oc op (arg ...) (z ... q) args)])) 

(define (ext-c oc c)
  (cond
    [(v:any/var? (oc->rands oc)) (cons oc c)]
    [else c]))
