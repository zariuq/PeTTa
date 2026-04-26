; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/functionhead.metta

(= (myfunc $A $B) (append (append (42) $A) $B))
(= (h_old $A $C) (if (= $A (myfunc (10) $B)) ($B $C) (empty)))
(= (h (myfunc (10) $B) $C) ($B $C))
!(assertPeTTaTest (h (42 10 40) 42000) ((40) 42000))
!(assertPeTTaTest (h_old (42 10 40) 42000) ((40) 42000))
