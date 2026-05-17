; Larger fold-nested/deep-nest slice that still aims to finish inside the profiling window.

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
   (if (is-expr $x)
       (fold-nested $f (fold-nested $f $init $x) $xs)
       (fold-nested $f ($f $init $x) $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))
(= (deep-nest $n) (if (== $n 0) () (cons (range 50) (deep-nest (- $n 1)))))

!(assertEqualToEval (fold-nested + 0 (deep-nest 5000)) 6375000)
