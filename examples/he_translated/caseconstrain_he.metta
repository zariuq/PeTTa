; Translated from PeTTa to HE (2 atoms)
; Source: examples/caseconstrain.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (case (1 2 3) (((cons $h $t) $h))) 1)
