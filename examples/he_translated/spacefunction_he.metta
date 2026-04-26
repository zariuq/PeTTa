; Translated from PeTTa to HE (16 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/spacefunction.metta

!(add-atom &self (= (f $x $y) (+ $x $y)))
!(add-atom &self (= (g $x $y) (+ $x $y)))
!(remove-atom &self (= (f $x $y) (+ $x $y)))
!(assertPeTTaTest (f 3 4) (f 3 4))
!(assertPeTTaTest (g 3 4) 7)
!(add-atom &self (my test))
!(remove-atom &self (my test))
!(assertPeTTaTest (collapse (match &self (my test) (my test))) ())
