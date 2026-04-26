(= (wrap2 $x) (Pair (S (S $x)) done))

!(assertPeTTaTest (wrap2 Z) (Pair (S (S Z)) done))
!(assertPeTTaTest (let (wrap2 $x) (Pair (S (S Z)) done) $x) Z)
