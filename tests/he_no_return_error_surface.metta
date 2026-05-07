!(assertEqualToResult
  (function (chain (+ 1 2) $x $x))
  ((Error (function (chain (+ 1 2) $x $x)) NoReturn)))
