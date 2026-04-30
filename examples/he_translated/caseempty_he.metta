; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/caseempty.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (wu) (case (empty) ((1 2) (Empty 42))))
(= (f) 42)
(= (wu2) (case (f) ((42 ok) (Empty nok))))
!(assertPeTTaTest (wu) 42)
!(assertPeTTaTest (wu2) ok)
