; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/partialdef.metta

(= (mp) (+))
!(assertPeTTaTest (mp 1 1) 2)
(= (.. $f1 $f2 $arg) ($f1 ($f2 $arg)))
(= (plus1times2) (.. (* 2) (+ 1)))
!(assertPeTTaTest (plus1times2 1) 4)
