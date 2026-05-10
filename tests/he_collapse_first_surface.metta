!(assertPeTTaTest
  (let $results (collapse (superpose (heads tails)))
       (if (== $results ())
           Empty
           (car-atom $results)))
  heads)

!(assertPeTTaTest
  (let $results (collapse (match &self absent $x))
       (if (== () $results)
           Empty
           (car-atom $results)))
  Empty)

!(assertPeTTaTest
  (chain (collapse (superpose (9 10))) $results
    (if (== $results ())
        Empty
        (car-atom $results)))
  9)
