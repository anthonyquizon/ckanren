#lang racket

(require cKanren/miniKanren
         (prefix-in fd: cKanren/unstable/fd))

(run 2 [q]
  (fresh [x y]
    (fd:infd x y '(1 2 3))
    (fd:+fd x y q)
    ;(== q x)
    
    ))
