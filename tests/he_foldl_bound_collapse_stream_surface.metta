(= (sum-collapse $n)
   (let $vals (collapse (superpose (1 2 3)))
     (foldl + $vals $n)))

!(assertEqual (sum-collapse 0) 6)
