; Small direct hyperpose stress repro.
; The first branch is intentionally expensive but finite, while the second
; branch is cheap. Real hyperpose should let the cheap branch satisfy `once`
; quickly; a sequential fallback has to wait for the burn branch first.

(= (burn $n)
   (if (== $n 0)
       False
       (burn (- $n 1))))

!(assertEqualToEval
  (once (hyperpose ((burn 2000000)
                    True)))
  True)
