(= (mymap $f ()) ())
(= (mymap $f (cons $x $xs)) (cons ($f $x) (mymap $f $xs)))

!(assertEqualToEval
  (mymap (== 1) (1 2 3))
  (true false false))
