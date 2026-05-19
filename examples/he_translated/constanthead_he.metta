; Translated from PeTTa to HE (3 atoms)
; Source: examples/constanthead.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (h (justdata haha $B) $C) (+ $B $C))
!(test (h (justdata haha 30) 40) 70)
