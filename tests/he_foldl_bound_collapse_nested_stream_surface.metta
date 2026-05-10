(= (sum-collapse-next $n)
   (let $vals (collapse (superpose (1 2 3)))
     (let $sum (foldl + $vals $n)
       $sum)))

!(assertEqual (sum-collapse-next 0) 6)
