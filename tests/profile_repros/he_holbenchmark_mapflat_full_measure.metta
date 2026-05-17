; Full-size map-flat/range slice from the translated holbenchmark example.

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))

!(assertEqualToEval (let $temp (map-flat (+ 1) (range 1000000)) (length $temp)) 1000000)
