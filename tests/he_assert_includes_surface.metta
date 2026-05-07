!(assertEqualToResult (assertIncludes (superpose (41 42 43)) (42)) (()))
!(assertEqualToResult
  (assertIncludes (superpose (41 42 43)) (A))
  ((Error (assertIncludes (superpose (41 42 43)) (A))
          (assertIncludes error: (A) not included in result: (41 42 43)))))
