; Full-size fold-nested/deep-nest slice from the translated holbenchmark example.

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
   (if (is-expr $x)
       (fold-nested $f (fold-nested $f $init $x) $xs)
       (fold-nested $f ($f $init $x) $xs)))
(= (range $n) (if (== $n 0) () (cons $n (range (- $n 1)))))
(= (deep-nest $n) (if (== $n 0) () (cons (range 50) (deep-nest (- $n 1)))))

!(assertPeTTaTest (fold-nested + 0 (deep-nest 20000)) 25500000)
