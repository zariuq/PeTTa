; Translated from PeTTa to HE (3 atoms)
; Source: examples/nestedcons.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f (cons $a (cons $b $L))) $b)
!(test (f (a b c d)) b)
