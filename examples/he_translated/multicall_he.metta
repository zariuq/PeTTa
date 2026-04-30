; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/multicall.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (mycalc $x $y) (+ $x $y))
(= (mycalc $x $y) (- $x $y))
!(assertPeTTaTest (collapse (mycalc 1 2)) (3 -1))
