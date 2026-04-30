; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/supercollapse.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (TupleConcat $Ev1 $Ev2) (collapse (superpose ((superpose $Ev1) (superpose $Ev2)))))
(= (range $K $N) (if (< $K $N) (TupleConcat ($K) (range (+ $K 1) $N)) ()))
!(assertPeTTaTest (range 1 10) (1 2 3 4 5 6 7 8 9))
