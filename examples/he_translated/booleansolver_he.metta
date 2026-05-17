; Translated from PeTTa to HE (2 atoms)
; Source: examples/booleansolver.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (if (and (or $x True) $y) ($x $y)) ((True True) (False True)))
