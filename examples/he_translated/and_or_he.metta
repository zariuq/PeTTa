; Translated from PeTTa to HE (2 atoms)
; Source: examples/and_or.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (if (or (and true false) true) 1 2) 1)
