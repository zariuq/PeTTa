; Translated from PeTTa to HE (19 atoms)
; Source: examples/functionremoval.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (g $x) (+ $x 1))
(= (f $g) ($g 1))
(= (f $g) 42)
!(assertEqualToEval (collapse (f g)) (2 42))
!(remove-atom &self (= (f $g) 42))
!(assertEqualToEval (collapse (f g)) (2))
!(add-atom &self (= (f $g) 42))
!(remove-atom &self (= (f $g) ($g 1)))
!(assertEqualToEval (collapse (f g)) (42))
!(remove-atom &self (= (f $g) 42))
!(assertEqualToEval (collapse (f g)) ((f g)))
