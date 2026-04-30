; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/nestedcons.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f (cons $a (cons $b $L))) $b)
!(assertPeTTaTest (f (a b c d)) b)
