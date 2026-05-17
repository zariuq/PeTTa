; Translated from PeTTa to HE (5 atoms)
; Source: examples/holfunctions_intrinsicop.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (mymap $f ()) ())
(= (mymap $f (cons $x $xs)) (cons ($f $x) (mymap $f $xs)))
(= (eq $a $b) (== $a $b))
!(assertEqualToEval (mymap (== 1) (1 2 3)) (mymap (eq 1) (1 2 3)))
