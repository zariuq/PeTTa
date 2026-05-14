; Larger map-flat/range slice that still aims to finish inside the profiling window.

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))

!(assertPeTTaTest (let $temp (map-flat (+ 1) (range 200000)) (length $temp)) 200000)
