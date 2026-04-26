; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/multicall.metta

(= (mycalc $x $y) (+ $x $y))
(= (mycalc $x $y) (- $x $y))
!(assertPeTTaTest (collapse (mycalc 1 2)) (3 -1))
