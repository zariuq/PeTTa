; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/caseempty.metta

(= (wu) (case (empty) ((1 2) (Empty 42))))
(= (f) 42)
(= (wu2) (case (f) ((42 ok) (Empty nok))))
!(assertPeTTaTest (wu) 42)
!(assertPeTTaTest (wu2) ok)
