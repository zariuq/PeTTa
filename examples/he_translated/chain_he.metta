; Translated from PeTTa to HE (4 atoms)
; Source: examples/chain.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (chain (+ 2 4) $n (* 3 $n)) 18)
!(assertEqualToEval (chain (+ 1 3) $n (chain (* 2 $n) $m (+ $n $m))) 12)
