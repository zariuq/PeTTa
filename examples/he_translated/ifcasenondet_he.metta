; Translated from PeTTa to HE (6 atoms)
; Source: examples/ifcasenondet.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (if-nondet $y) (if (superpose $y) a b))
(= (case-nondet $y) (case (superpose $y) ((True a) (False b))))
!(assertEqualToEval (collapse (if-nondet (True False True))) (a b a))
!(assertEqualToEval (collapse (case-nondet (True False True))) (a b a))
