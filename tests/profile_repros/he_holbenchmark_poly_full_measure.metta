; Full-size poly slice from the translated holbenchmark example.

(= (poly $f $n) (if (== $n 0) 0 (+ ($f $n) (poly $f (- $n 1)))))

!(assertEqualToEval (poly (+ 1) 1000000) 500001500000)
