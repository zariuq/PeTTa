; Translated from PeTTa to HE (5 atoms)
; Source: examples/xor.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (check_xor $source $destination) (if (xor (== $source $destination) (> $source $destination)) 42 0))
!(assertEqualToEval (check_xor 2 2) 42)
!(assertEqualToEval (check_xor 4 2) 42)
