(= (two-results) 3)
(= (two-results) 2)
(= (tuple-result) (3 2))

!(assertEqualToEval (+ 1 2) 3)
!(assertEqualToEval (tuple-result) (3 2))
!(assertEqualToEval (two-results) (3 2))
!(assertEqualToEval %Undefined% $anything)
