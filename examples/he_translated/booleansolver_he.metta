; Translated from PeTTa to HE (2 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/booleansolver.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (if (and (or $x True) $y) ($x $y)) ((True True) (False True)))
