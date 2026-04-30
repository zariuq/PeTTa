; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/ifcasenondet.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (if-nondet $y) (if (superpose $y) a b))
(= (case-nondet $y) (case (superpose $y) ((True a) (False b))))
!(assertPeTTaTest (collapse (if-nondet (True False True))) (a b a))
!(assertPeTTaTest (collapse (case-nondet (True False True))) (a b a))
