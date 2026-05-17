(= (wrap2 $x) (Pair (S (S $x)) done))

!(assertEqualToEval (wrap2 Z) (Pair (S (S Z)) done))
!(assertEqualToEval (let (wrap2 $x) (Pair (S (S Z)) done) $x) Z)
