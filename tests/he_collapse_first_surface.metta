!(assertEqualToEval
  (let $results (collapse (superpose (heads tails)))
       (if (== $results ())
           Empty
           (car-atom $results)))
  heads)

!(assertEqualToEval
  (let $results (collapse (match &self absent $x))
       (if (== () $results)
           Empty
           (car-atom $results)))
  Empty)

!(assertEqualToEval
  (chain (collapse (superpose (9 10))) $results
    (if (== $results ())
        Empty
        (car-atom $results)))
  9)
