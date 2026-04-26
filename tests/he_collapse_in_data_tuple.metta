(= (tuple-with-collapse)
   ((collapse (superpose (a b c)))
    (collapse (superpose ((superpose (x y)))))))

!(assertPeTTaTest (tuple-with-collapse) ((a b c) (x y)))
