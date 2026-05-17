(= (tuple-with-collapse)
   ((collapse (superpose (a b c)))
    (collapse (superpose ((superpose (x y)))))))

!(assertEqualToEval (tuple-with-collapse) ((a b c) (x y)))
