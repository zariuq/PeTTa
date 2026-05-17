; Translated from PeTTa to HE (14 atoms)
; Source: examples/spaces3.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering


!(add-atom &wuspace (wu))
!(add-atom &wuspace (wu 42))
!(assertEqualToEval (collapse (match &wuspace ($1) ($1))) ((wu)))
!(assertEqualToEval (collapse (match &wuspace ($1) (hu $1))) ((hu wu)))
!(assertEqualToEval (collapse (match &wuspace ($1) $1)) (wu))
!(assertEqualToEval (msort (collapse (match &wuspace $1 $1))) (msort (collapse (get-atoms &wuspace))))
!(assertEqualToEval (msort (collapse (match &wuspace $1 (wu $1)))) ((wu (wu)) (wu (wu 42))))
