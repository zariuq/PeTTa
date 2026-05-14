; Reduced HE witness for the fold-nested family from holbenchmark.
; This isolates recursive higher-order binary application over nested data
; without the separate map/range and poly/apply-many lanes.

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
   (if (is-expr $x)
       (fold-nested $f (fold-nested $f $init $x) $xs)
       (fold-nested $f ($f $init $x) $xs)))

(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

(= (deep-nest $n)
   (if (== $n 0) ()
       (cons (range 50) (deep-nest (- $n 1)))))

!(test (fold-nested + 0 (deep-nest 200))
       255000)
