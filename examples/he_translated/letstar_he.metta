; Translated from PeTTa to HE (2 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/letstar.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (let* (($x 1) ($y 2)) (+ $x $y)) 3)
