(= (push-item $x $xs) (cons $x $xs))
!(assertEqualToEval (foldl + (1 2 3) 0) 6)
!(assertEqualToEval (foldl push-item (a b) ()) (b a))
