!(assertEqualToEval
  (=alpha
    (alpha-unique-atom ((link $x human) (link $y human)))
    ((link $a human)))
  True)
