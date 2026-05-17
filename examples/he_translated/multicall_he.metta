; Translated from PeTTa to HE (4 atoms)
; Source: examples/multicall.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (mycalc $x $y) (+ $x $y))
(= (mycalc $x $y) (- $x $y))
!(assertEqualToEval (collapse (mycalc 1 2)) (3 -1))
