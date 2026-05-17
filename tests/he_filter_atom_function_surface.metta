(= (filterfun $x) (> $x 3))

!(assertEqualToEval
  (filter-atom (1 2 3 4 5) filterfun)
  (4 5))
