; Probe whether HE evaluates nested arithmetic inside == the same way as PeTTa.

!(assertEqualToEval
  (== 0 (% 4 2))
  True)

!(assertEqualToEval
  (== 1 (% 5 2))
  True)
