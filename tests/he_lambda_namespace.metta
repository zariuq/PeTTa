; Lambda closures keep their MeTTa-facing symbol, but under --he their
; compiled predicate must live in the private user-head namespace.

!(assertEqual ((|-> ($x) (+ $x 1)) 2) 3)

!(assertEqual
  (let $f (|-> ($x $y) (+ $x $y))
       (eval ($f 2 3)))
  5)

!(assertEqual
  (maplist (|-> ($x) (+ $x 1)) (1 2 3))
  (2 3 4))
