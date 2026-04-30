; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/fibsmartimport.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self ../fibsmart.metta)
!(assertPeTTaTest (fib 100) 354224848179261915075)
