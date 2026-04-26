; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/letlet.metta

(= (f) (let* ((($f1 $c1 3) (1 2 $d1))) ($f1 $c1 $d1)))
!(assertPeTTaTest (f) (1 2 3))
