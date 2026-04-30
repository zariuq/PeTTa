; Sequential fallback counterpart for hyperpose_once_burn_vs_true.metta.
; This mirrors the canonical translator's default hyperpose -> superpose
; lowering so we can compare direct PeTTa --he extension behavior against
; portable sequential fallback. Under this fallback, `once` observes the
; first branch's result rather than the first branch to finish.

(= (burn $n)
   (if (== $n 0)
       False
       (burn (- $n 1))))

!(assertPeTTaTest
  (once (superpose ((burn 2000000)
                    True)))
  False)
