; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/patrick_iterate_quad.metta

!(import! &self (library lib_patrick))
(= (quad-step $dummy ($t $i $sum)) (if (== $i $t) ((+ $t 1) 1 (+ $sum (* $t $i))) ($t (+ $i 1) (+ $sum (* $t $i)))))
(= (quad-sum $n) (last (iterate 0 (/ (* $n (+ $n 1)) 2) (1 1 0) quad-step)))
!(assertPeTTaTest (quad-sum 1000) 125417041750)
