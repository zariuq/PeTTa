(= (poly $f $n)
   (if (== $n 0)
       0
       (+ ($f $n)
          (poly $f (- $n 1)))))

!(assertPeTTaTest (poly (+ 1) 5) 20)
!(assertPeTTaTest (poly (+ 2) 5) 25)
!(assertEqual (poly (+ 1) foo) (poly (+ 1) foo))
