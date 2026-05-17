; Translated from PeTTa to HE (2 atoms)
; Source: examples/if.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (if (> 1 2) (3 4) (5 6)) (5 6))
