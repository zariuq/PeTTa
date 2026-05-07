(= (coin) (superpose (heads tails)))

!(assertEqualToResult (eval (coin)) ((superpose (heads tails))))
!(assertEqualToResult (collapse (eval (coin))) (((superpose (heads tails)))))
