; Translated from PeTTa to HE (3 atoms)
; Source: examples/factorial.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (facF $n) (if (== $n 0) 1 (* $n (facF (- $n 1)))))
!(test (facF 10) 3628800)
