; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/identity.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f $x) (* $x $x))
!(assertPeTTaTest (f 1) 1)
