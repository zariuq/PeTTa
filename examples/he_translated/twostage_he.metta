; Translated from PeTTa to HE (7 atoms)
; Source: examples/twostage.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) (g))
(= (g) 42)
(= (h) (g))
!(test (f) 42)
!(test (h) 42)
