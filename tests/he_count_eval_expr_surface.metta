(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))

!(assertEqual (length (map-flat (+ 1) (range 10))) 10)
!(assertEqual (length (range 7)) 7)
!(assertEqual (length (cons foo (cons bar ()))) 2)
