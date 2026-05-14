; Reduced HE witness for the map-flat/range family from holbenchmark.
; This isolates higher-order unary recursion plus list growth/counting from
; the fold-nested and poly/apply-many lanes.

(= (count-demo $expr)
   (let $tuple (eval $expr)
        (size-atom $tuple)))

(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))

(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

!(test (let $temp (map-flat (+ 1) (range 5000))
          (count-demo $temp))
       5000)
