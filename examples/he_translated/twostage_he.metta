; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/twostage.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) (g))
(= (g) 42)
(= (h) (g))
!(assertPeTTaTest (f) 42)
!(assertPeTTaTest (h) 42)
