; Translated from PeTTa to HE (6 atoms)
; Source: examples/patrick_iterate_quad.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self (library lib_patrick))
(= (quad-step $dummy ($t $i $sum)) (if (== $i $t) ((+ $t 1) 1 (+ $sum (* $t $i))) ($t (+ $i 1) (+ $sum (* $t $i)))))
(= (quad-sum $n) (last (iterate 0 (/ (* $n (+ $n 1)) 2) (1 1 0) quad-step)))
!(assertEqualToEval (quad-sum 1000) 125417041750)
