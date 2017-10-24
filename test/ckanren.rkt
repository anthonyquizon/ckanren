#lang racket

(require 
  "../src/ckanren.rkt"
  "../src/minikanren.rkt"
  rackunit)

(check-equal? 
  (run [q]
    (fresh [x]
      (== x 5)
      (== q x)))
  '((((#(0) . 5)) . 1)))
