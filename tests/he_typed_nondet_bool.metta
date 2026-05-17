!(assertEqualToEval
  (collapse (if (and (or $x True) $y) ($x $y)))
  ((True True) (False True)))
