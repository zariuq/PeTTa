!(assertEqual (foldl + (collapse (superpose (1 2 3))) 0) 6)
!(assertEqual (foldl + (collapse (superpose ((/ 1 0) 1 2))) 0) 3)
