; Translated from PeTTa to HE (5 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/xor.metta

(= (check_xor $source $destination) (if (xor (== $source $destination) (> $source $destination)) 42 0))
!(assertPeTTaTest (check_xor 2 2) 42)
!(assertPeTTaTest (check_xor 4 2) 42)
