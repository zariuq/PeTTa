; Translated from PeTTa to HE (5 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/casenew.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (wu1) (empty))
(= (wu2) (full))
(= (wu) (superpose ((wu1) (wu2))))
!(assertPeTTaTest (wu) (full))
