!(assertEqual (collapse Empty) ())
!(assertEqualToResult (superpose (a Empty b)) (a b))
!(assertEqual (collapse (superpose (a Empty b))) (a b))
!(assertEqual (once (superpose ())) Empty)
