!(assertEqualToEval
  (length (collapse (superpose (1 2 3 4))))
  4)

!(assertEqualToEval
  (let $tuple (collapse (superpose ((Error boom bad) 7 8)))
       (size-atom $tuple))
  2)
