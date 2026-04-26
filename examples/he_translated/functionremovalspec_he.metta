; Translated from PeTTa to HE (13 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/functionremovalspec.metta

(= (g $x) (+ $x 1))
(= (f $g) ($g 1))
(= (f $g) ($g 2))
!(assertPeTTaTest (collapse (f g)) (2 3))
!(remove-atom &self (= (f $g) ($g 1)))
!(assertPeTTaTest (f g) 3)
!(add-atom &self (= (f $g) ($g 1)))
!(assertPeTTaTest (f g) (3 2))
