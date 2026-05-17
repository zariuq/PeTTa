; Translated from PeTTa to HE (4 atoms)
; Source: examples/library.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self (library lib_roman))
!(assertEqualToEval (map-flat (+ 1) (1 2 3)) (2 3 4))
