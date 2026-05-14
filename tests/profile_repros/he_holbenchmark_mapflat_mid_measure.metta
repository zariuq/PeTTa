; Mid-size map-flat/range slice that aims to preserve the full-family cost
; while still finishing cleanly under the profiler.

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))

!(assertPeTTaTest (let $temp (map-flat (+ 1) (range 100000)) (length $temp)) 100000)
