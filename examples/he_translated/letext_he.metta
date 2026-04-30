; Translated from PeTTa to HE (2 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/letext.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (let ($x (42 (if (== $x 2) 43 44))) (3 (42 $z)) (+ $x $z)) 47)
