; Translated from PeTTa to HE (16 atoms)
; Source: examples/spacefunction.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(add-atom &self (= (f $x $y) (+ $x $y)))
!(add-atom &self (= (g $x $y) (+ $x $y)))
!(remove-atom &self (= (f $x $y) (+ $x $y)))
!(assertEqualToEval (f 3 4) (f 3 4))
!(assertEqualToEval (g 3 4) 7)
!(add-atom &self (my test))
!(remove-atom &self (my test))
!(assertEqualToEval (collapse (match &self (my test) (my test))) ())
