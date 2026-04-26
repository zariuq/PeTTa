; Translated from PeTTa to HE (19 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/functionremoval.metta

(= (g $x) (+ $x 1))
(= (f $g) ($g 1))
(= (f $g) 42)
!(assertPeTTaTest (collapse (f g)) (2 42))
!(remove-atom &self (= (f $g) 42))
!(assertPeTTaTest (collapse (f g)) (2))
!(add-atom &self (= (f $g) 42))
!(remove-atom &self (= (f $g) ($g 1)))
!(assertPeTTaTest (collapse (f g)) (42))
!(remove-atom &self (= (f $g) 42))
!(assertPeTTaTest (collapse (f g)) ((f g)))
