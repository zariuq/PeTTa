; Translated from PeTTa to HE (3 atoms)
; Source: examples/empty.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (y) (empty))
!(test (collapse (y)) ())
