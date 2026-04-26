; Translated from PeTTa to HE (5 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/holfunctions_intrinsicop.metta

(= (mymap $f ()) ())
(= (mymap $f (cons $x $xs)) (cons ($f $x) (mymap $f $xs)))
(= (eq $a $b) (== $a $b))
!(assertPeTTaTest (mymap (== 1) (1 2 3)) (mymap (eq 1) (1 2 3)))
