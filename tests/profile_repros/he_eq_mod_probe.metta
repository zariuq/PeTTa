; Probe whether HE evaluates nested arithmetic inside == the same way as PeTTa.

!(assertPeTTaTest
  (== 0 (% 4 2))
  True)

!(assertPeTTaTest
  (== 1 (% 5 2))
  True)
