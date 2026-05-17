(= (STV a) (stv 0.4 0.9))
(= (use-stv (stv $s $c)) (ok $s $c))

!(assertEqualToEval
  (use-stv (STV a))
  (ok 0.4 0.9))
