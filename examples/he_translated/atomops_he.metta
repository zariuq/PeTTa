; Translated from PeTTa to HE (18 atoms)
; Source: examples/atomops.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (cons-atom 0 (1 2 3)) (0 1 2 3))
!(assertEqualToEval (car-atom (1 2 3)) 1)
!(assertEqualToEval (cdr-atom (1 2 3)) (2 3))
!(assertEqualToEval (index-atom (1 2 3) 1) 2)
!(assertEqualToEval (id 5) 5)
!(assertEqualToEval (=alpha (Father $X) (Father $Y)) True)
!(assertEqualToEval (=alpha (Father $X) (Son $X)) False)
!(assertEqualToEval (first-from-pair (A B)) A)
!(assertEqualToEval (second-from-pair (A B)) B)
