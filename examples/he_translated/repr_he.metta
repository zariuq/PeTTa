; Translated from PeTTa to HE (12 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/repr.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (repr 42) "42")
!(assertPeTTaTest (repr "42") "\"42\"")
!(assertPeTTaTest (repr (A (B C))) "(A (B C))")
!(assertPeTTaTest (repr (A (, B , C ,))) "(A (, B , C ,))")
!(assertPeTTaTest (repr 2025_12_12) "2025_12_12")
!(assertPeTTaTest (repr ()) "()")
