#lang racket

(require 
  "../src/core.rkt"
  (prefix-in u: rackunit))

(u:check-equal?
  (run* [q]
    (== q 1))
  '((1)))

