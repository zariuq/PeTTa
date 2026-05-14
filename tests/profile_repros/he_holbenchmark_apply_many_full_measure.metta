; Full-size apply-many slice from the translated holbenchmark example.

(= (apply-many $f $n $x) (if (== $n 0) $x (apply-many $f (- $n 1) ($f $x))))

!(assertPeTTaTest (apply-many (+ 1) 100000 0) 100000)
