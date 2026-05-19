; Translated from PeTTa to HE (3 atoms)
; Source: examples/superpose_nested.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (program) ((collapse (superpose ((superpose (a b c)) (superpose (x y z))))) (collapse (superpose (a b c))) (collapse (superpose ((superpose (a b c))))) (collapse (superpose ((superpose (a b c)) x y z)))))
!(test (program) ((a b c x y z) (a b c) (a b c) (a b c x y z)))
