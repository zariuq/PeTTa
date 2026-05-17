(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

!(assertEqualToEval (range 5) (5 4 3 2 1))
!(assertEqualToEval (range 0) ())
