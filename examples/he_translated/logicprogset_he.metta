; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/logicprogset.metta

(= (myf $M) (and (and (member a $M) (member b $M)) (== (size-atom $M) 2)))
!(assertPeTTaTest (if (once (myf $M)) $M) (a b))
