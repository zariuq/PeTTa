; Translated from PeTTa to HE (8 atoms)
; Source: examples/multiset_operations.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(test (unique-atom (a b c d d)) (a b c d))
!(test (union-atom (a b b c) (b c c d)) (a b b c b c c d))
!(test (intersection-atom (a b c c) (b c c c d)) (b c c))
!(test (subtraction-atom (a b b c) (b c c d)) (a b))
