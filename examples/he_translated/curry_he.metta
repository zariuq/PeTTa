; Translated from PeTTa to HE (16 atoms)
; Source: examples/curry.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f $a $b) (+ $a $b))
(= (g $a $b $c) (+ $c (+ $a $b)))
(= (show) (repr (f 1)))
!(assertEqualToEval (repr (f 1)) "(partial f (1))")
!(assertEqualToEval ((f 1) 2) 3)
!(assertEqualToEval (repr (g 1 2)) "(partial g (1 2))")
(= (h $A $B) (append ($A) $B))
!(assertEqualToEval ((h 42) (1 2 3)) (42 1 2 3))
!(assertEqualToEval (repr (h 42)) "(partial h (42))")
!(assertEqualToEval (map-atom (1 2 3) (+ 1)) (2 3 4))
