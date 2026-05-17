(= (paircallx $f $x) (($f $x) ($f $x)))
!(assertEqualToEval (paircallx (+ 2) 1) (3 3))
