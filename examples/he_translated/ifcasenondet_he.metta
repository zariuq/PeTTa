; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/ifcasenondet.metta

(= (if-nondet $y) (if (superpose $y) a b))
(= (case-nondet $y) (case (superpose $y) ((True a) (False b))))
!(assertPeTTaTest (collapse (if-nondet (True False True))) (a b a))
!(assertPeTTaTest (collapse (case-nondet (True False True))) (a b a))
