(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

!(assertPeTTaTest (range 5) (5 4 3 2 1))
!(assertPeTTaTest (range 0) ())
