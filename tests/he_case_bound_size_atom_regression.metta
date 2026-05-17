!(assertEqualToEval
  (case (collected (a b) ())
    (((collected $body $rest)
      (if (== (size-atom $body) 2)
          ok
          bad))
     (parse-unsupported parse-unsupported)))
  ok)
