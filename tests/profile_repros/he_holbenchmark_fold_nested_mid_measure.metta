; Mid-size fold-nested/deep-nest slice that aims to preserve the full-family
; recursion shape while still finishing cleanly under the profiler.

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
   (if (is-expr $x)
       (fold-nested $f (fold-nested $f $init $x) $xs)
       (fold-nested $f ($f $init $x) $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))
(= (deep-nest $n) (if (== $n 0) () (cons (range 50) (deep-nest (- $n 1)))))

!(assertEqualToEval (fold-nested + 0 (deep-nest 1000)) 1275000)
