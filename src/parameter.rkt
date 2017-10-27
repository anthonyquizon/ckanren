#lang racket

(provide
  process-prefix
  enforce-constraints
  reify-constraints)

(define process-prefix (make-parameter 'dummy))
(define enforce-constraints (make-parameter 'dummy))
(define reify-constraints (make-parameter 'dummy))
