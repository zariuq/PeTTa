; Translated from PeTTa to HE (12 atoms)
; Source: examples/repr.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(test (repr 42) "42")
!(test (repr "42") "\"42\"")
!(test (repr (A (B C))) "(A (B C))")
!(test (repr (A (, B , C ,))) "(A (, B , C ,))")
!(test (repr 2025_12_12) "2025_12_12")
!(test (repr ()) "()")
