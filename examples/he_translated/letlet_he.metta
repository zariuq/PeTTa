; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/letlet.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) (let* ((($f1 $c1 3) (1 2 $d1))) ($f1 $c1 $d1)))
!(assertPeTTaTest (f) (1 2 3))
