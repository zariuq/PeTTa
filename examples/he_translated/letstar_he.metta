; Translated from PeTTa to HE (2 atoms)
; Source: examples/letstar.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(test (let* (($x 1) ($y 2)) (+ $x $y)) 3)
