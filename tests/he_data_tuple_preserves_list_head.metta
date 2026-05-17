(= (list-head-data-tuple)
   ((1 2 3) (+ 1 1)))

!(assertEqualToResult
  (list-head-data-tuple)
  (((1 2 3) 2)))
