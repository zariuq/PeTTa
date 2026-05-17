(= (paircallatom $x) ((+ $x 1) (+ $x 2)))
!(assertEqualToEval (paircallatom 1) (2 3))
