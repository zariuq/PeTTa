; Translated from PeTTa to HE (8 atoms)
; Source: examples/multiset_operations.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (unique-atom (a b c d d)) (a b c d))
!(assertEqualToEval (union-atom (a b b c) (b c c d)) (a b b c b c c d))
!(assertEqualToEval (intersection-atom (a b c c) (b c c c d)) (b c c))
!(assertEqualToEval (subtraction-atom (a b b c) (b c c d)) (a b))
