; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/chain.metta

!(assertPeTTaTest (chain (+ 2 4) $n (* 3 $n)) 18)
!(assertPeTTaTest (chain (+ 1 3) $n (chain (* 2 $n) $m (+ $n $m))) 12)
