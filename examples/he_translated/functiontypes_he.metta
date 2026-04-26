; Translated from PeTTa to HE (14 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/functiontypes.metta

(: wu1 (-> Number Expression Expression))
(= (wu1 $a $b) (42 $a $b))
(: wu2 (-> Number Number Number))
(= (wu2 $a $b) (+ $a $b))
(: wu3 (-> Number Number %Undefined%))
(= (wu3 $a $b) (if (< $a 10) (+ $a $b) (a list not a number)))
!(assertPeTTaTest (wu1 (+ 2 4) (+ 4 2)) (quote (42 6 (+ 4 2))))
!(assertPeTTaTest (wu2 (+ 2 4) (+ 4 2)) 12)
!(assertPeTTaTest (wu3 42 0) (a list not a number))
!(assertPeTTaTest (wu3 2 0) 2)
