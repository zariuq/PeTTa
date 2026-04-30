; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/constanthead.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (h (justdata haha $B) $C) (+ $B $C))
!(assertPeTTaTest (h (justdata haha 30) 40) 70)
