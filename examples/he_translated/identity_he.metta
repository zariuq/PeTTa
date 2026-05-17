; Translated from PeTTa to HE (3 atoms)
; Source: examples/identity.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f $x) (* $x $x))
!(assertEqualToEval (f 1) 1)
