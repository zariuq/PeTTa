(= (div-direct $x $y $accum)
   (if (< (- $x $y) 0)
       $accum
       (div-direct (- $x $y) $y (+ 1 $accum))))

!(test (div-direct 350000 5 0) 70000)
