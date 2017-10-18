#lang racket

(require 
  (prefix-in fd: "../src/ckanren.rkt")
  "../src/minikanren.rkt")

(run [q]
  (fresh [x y z]
    (fd:in x z (range 3 5))
    (fd:in y (range 1 4))
    (fd:< x 5) 
    (== x y)
    (== q `(,y ,z))))
