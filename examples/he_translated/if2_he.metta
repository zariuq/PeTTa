; Translated from PeTTa to HE (2 atoms)
; Source: examples/if2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(test (if (is-var a) (() (+ 1 1)) (+ 2 2)) 4)
