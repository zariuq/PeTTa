; Translated from PeTTa to HE (14 atoms)
; Source: examples/functiontypes.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
(: wu1 (-> Number Expression Expression))
(= (wu1 $a $b) (42 $a $b))
(: wu2 (-> Number Number Number))
(= (wu2 $a $b) (+ $a $b))
(: wu3 (-> Number Number %Undefined%))
(= (wu3 $a $b) (if (< $a 10) (+ $a $b) (a list not a number)))
!(assertEqualToEval (wu1 (+ 2 4) (+ 4 2)) (quoted-syntax (quote (42 6 (+ 4 2)))))
!(assertEqualToEval (wu2 (+ 2 4) (+ 4 2)) 12)
!(assertEqualToEval (wu3 42 0) (a list not a number))
!(assertEqualToEval (wu3 2 0) 2)
