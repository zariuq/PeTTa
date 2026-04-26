(= (push-item $x $xs) (cons $x $xs))
!(assertPeTTaTest (foldl + (1 2 3) 0) 6)
!(assertPeTTaTest (foldl push-item (a b) ()) (b a))
