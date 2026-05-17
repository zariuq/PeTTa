; Small direct HE++ hyperpose smoke.
; The expensive branch should not block once from taking the cheap success.

(= (burn $n)
   (if (== $n 0)
       False
       (burn (- $n 1))))

!(assertEqualToEval
  (once (hyperpose ((burn 2000000)
                    True)))
  True)
