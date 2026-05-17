; Translated from PeTTa to HE (11 atoms)
; Source: examples/spaces2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(foo 1)
(foo 2)
(foo 42 42)
(foo (42 42))
!(bar 42)
!(bar 43)
(= (answer) 42)
!(assertEqualToEval (space (msort (collapse (superpose ((match &self (foo $1) (foo $1)) (match &self (foo $1 $2) (foo $1 $2)) (match &self (bar $1) (bar $1)))))) (answer)) (space ((foo 1) (foo 2) (foo 42 42) (foo (42 42))) 42))
