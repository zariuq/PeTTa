(= (two-results) 3)
(= (two-results) 2)
(= (tuple-result) (3 2))

!(assertPeTTaTest (+ 1 2) 3)
!(assertPeTTaTest (tuple-result) (3 2))
!(assertPeTTaTest (two-results) (3 2))
!(assertPeTTaTest %Undefined% $anything)
