; Registered incomplete calls should remain callable partial closures under
; PeTTa --he. Truly unknown calls still remain data.

(= (partial-cons $a $b) (cons $a $b))

!(assertEqual
  (let $f (partial-cons 42)
       ($f (43 2 3)))
  (42 43 2 3))

!(assertEqual
  (unknown-partial-probe 42)
  (unknown-partial-probe 42))

!(assertEqual
  (map-atom (1 2 3) (+ 1))
  (2 3 4))
