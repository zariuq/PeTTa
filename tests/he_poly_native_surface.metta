(= (poly $f $n)
   (if (== $n 0)
       0
       (+ ($f $n)
          (poly $f (- $n 1)))))

!(assertEqualToEval (poly (+ 1) 5) 20)
!(assertEqualToEval (poly (+ 2) 5) 25)
!(assertEqual (poly (+ 1) foo) (poly (+ 1) foo))
