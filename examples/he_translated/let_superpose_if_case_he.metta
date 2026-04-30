; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/let_superpose_if_case.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f $x) 42)
(= (progme) (let $y (superpose (2 3 4 5)) (if (> $y 2) (case (1 $y) (((1 3) (f 0)) ((1 4) (42 42)) ($else (42 42 42)))) answertoeverything)))
!(assertPeTTaTest (collapse (progme)) (answertoeverything 42 (42 42) (42 42 42)))
