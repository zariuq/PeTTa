; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/nestedcons.metta

(= (f (cons $a (cons $b $L))) $b)
!(assertPeTTaTest (f (a b c d)) b)
