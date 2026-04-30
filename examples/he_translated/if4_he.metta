; Translated from PeTTa to HE (2 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/if4.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (if (if (== 42 42) True False) (if True 42 lol) (+ 2 2)) 42)
