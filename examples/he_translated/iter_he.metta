; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/iter.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (make-nat-iter) 0)
(= (iter-next $N) (let* (($X $N) ($Next (+ $N 1))) ($X $Next)))
!(assertPeTTaTest (let* (($it (make-nat-iter)) (($x1 $it1) (iter-next $it)) (($x2 $it2) (iter-next $it1)) (($x3 $it3) (iter-next $it2))) ($x1 $x2 $x3)) (0 1 2))
