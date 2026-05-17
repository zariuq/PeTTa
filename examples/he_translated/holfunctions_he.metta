; Translated from PeTTa to HE (24 atoms)
; Source: examples/holfunctions.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f1a) (foldl-atom (1 2 3 4) 0 $acc $x (+ $acc $x)))
(= (f2a) (map-atom (1 2 3) $x (+ $x 1)))
(= (f3a) (filter-atom (1 2 3 4 5) $x (> $x 3)))
(= (foldfun $a $b) (+ $a $b))
(= (mapfun $a) (+ $a 1))
(= (filterfun $x) (> $x 3))
(= (f1b) (foldl-atom (1 2 3 4) 0 $__tr_acc_1 $__tr_item_2 (eval (foldfun $__tr_acc_1 $__tr_item_2))))
(= (f2b) (map-atom (1 2 3) mapfun))
(= (f3b) (filter-atom (1 2 3 4 5) filterfun))
!(assertEqualToEval (f1a) 10)
!(assertEqualToEval (f2a) (2 3 4))
!(assertEqualToEval (f3a) (4 5))
!(assertEqualToEval (f1b) 10)
!(assertEqualToEval (f2b) (2 3 4))
!(assertEqualToEval (f3b) (4 5))
(= (foldfun2 $a $b) (append $a $b))
!(foldl-atom ((1 2) (3 4) (5 6)) () $acc $x (append $acc $x))
