; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/partialdef.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (mp) (+))
!(assertPeTTaTest (mp 1 1) 2)
(= (.. $f1 $f2 $arg) ($f1 ($f2 $arg)))
(= (plus1times2) (.. (* 2) (+ 1)))
!(assertPeTTaTest (plus1times2 1) 4)
