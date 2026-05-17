; Translated from PeTTa to HE (14 atoms)
; Source: examples/functionhead3.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (in $x $L) (let True (is-member $x $L) $x))
(= (myplus (in $X (1 2 3)) (in $Y (2 3))) (in (+ $X $Y) (3 4 5)))
!(assertEqualToEval (collapse (myplus 1 3)) (4))
!(assertEqualToEval (collapse (myplus 3 3)) ())
!(assertEqualToEval (collapse (myplus 3 4)) ())
!(assertEqualToEval (collapse (myplus $x 3)) (4 5))
!(assertEqualToEval (collapse (myplus $x $y)) (3 4 4 5 5))
!(assertEqualToEval (collapse (let True (> (myplus $x 2) 3) $x)) (2 3))
