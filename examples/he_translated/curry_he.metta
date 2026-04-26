; Translated from PeTTa to HE (16 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/curry.metta

(= (f $a $b) (+ $a $b))
(= (g $a $b $c) (+ $c (+ $a $b)))
(= (show) (repr (f 1)))
!(assertPeTTaTest (repr (f 1)) "(partial f (1))")
!(assertPeTTaTest ((f 1) 2) 3)
!(assertPeTTaTest (repr (g 1 2)) "(partial g (1 2))")
(= (h $A $B) (append ($A) $B))
!(assertPeTTaTest ((h 42) (1 2 3)) (42 1 2 3))
!(assertPeTTaTest (repr (h 42)) "(partial h (42))")
!(assertPeTTaTest (map-atom (1 2 3) (+ 1)) (2 3 4))
