; Translated from PeTTa to HE (12 atoms)
; Source: examples/repr.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (repr 42) "42")
!(assertEqualToEval (repr "42") "\"42\"")
!(assertEqualToEval (repr (A (B C))) "(A (B C))")
!(assertEqualToEval (repr (A (, B , C ,))) "(A (, B , C ,))")
!(assertEqualToEval (repr 2025_12_12) "2025_12_12")
!(assertEqualToEval (repr ()) "()")
