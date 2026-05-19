(= (program)
   ((collapse (superpose ((superpose (a b c)) (superpose (x y z)))))
    (collapse (superpose (a b c)))
    (collapse (superpose ((superpose (a b c)))))
    (collapse (superpose ((superpose (a b c)) x y z )))))

!(test (program)
       ((a b c x y z) (a b c) (a b c) (a b c x y z)))
