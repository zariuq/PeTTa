; Translated from PeTTa to HE (18 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/atomops.metta

!(assertPeTTaTest (cons-atom 0 (1 2 3)) (0 1 2 3))
!(assertPeTTaTest (car-atom (1 2 3)) 1)
!(assertPeTTaTest (cdr-atom (1 2 3)) (2 3))
!(assertPeTTaTest (index-atom (1 2 3) 1) 2)
!(assertPeTTaTest (id 5) 5)
!(assertPeTTaTest (=alpha (Father $X) (Father $Y)) True)
!(assertPeTTaTest (=alpha (Father $X) (Son $X)) False)
!(assertPeTTaTest (first-from-pair (A B)) A)
!(assertPeTTaTest (second-from-pair (A B)) B)
