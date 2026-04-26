; Translated from PeTTa to HE (8 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/multiset_operations.metta

!(assertPeTTaTest (unique-atom (a b c d d)) (a b c d))
!(assertPeTTaTest (union-atom (a b b c) (b c c d)) (a b b c b c c d))
!(assertPeTTaTest (intersection-atom (a b c c) (b c c c d)) (b c c))
!(assertPeTTaTest (subtraction-atom (a b b c) (b c c d)) (a b))
