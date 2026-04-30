; Translated from PeTTa to HE (8 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/multiset_operations.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (unique-atom (a b c d d)) (a b c d))
!(assertPeTTaTest (union-atom (a b b c) (b c c d)) (a b b c b c c d))
!(assertPeTTaTest (intersection-atom (a b c c) (b c c c d)) (b c c))
!(assertPeTTaTest (subtraction-atom (a b b c) (b c c d)) (a b))
