; Translated from PeTTa to HE (7 atoms)
; Source: examples/partialdef.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (mp) (+))
!(assertEqualToEval (mp 1 1) 2)
(= (.. $f1 $f2 $arg) ($f1 ($f2 $arg)))
(= (plus1times2) (.. (* 2) (+ 1)))
!(assertEqualToEval (plus1times2 1) 4)
