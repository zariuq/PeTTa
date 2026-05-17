!(assertEqualToEval
  ((if True (let $f (|-> ($x) (+ $x 1)) $f) (empty)) 2)
  3)
