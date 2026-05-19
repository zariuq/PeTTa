; Translated from PeTTa to HE (4 atoms)
; Source: examples/fibsmartimport.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self ../fibsmart.metta)
!(test (fib 100) 354224848179261915075)
