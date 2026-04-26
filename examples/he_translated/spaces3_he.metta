; Translated from PeTTa to HE (14 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/spaces3.metta

!(add-atom &wuspace (wu))
!(add-atom &wuspace (wu 42))
!(assertPeTTaTest (collapse (match &wuspace ($1) ($1))) ((wu)))
!(assertPeTTaTest (collapse (match &wuspace ($1) (hu $1))) ((hu wu)))
!(assertPeTTaTest (collapse (match &wuspace ($1) $1)) (wu))
!(assertPeTTaTest (msort (collapse (match &wuspace $1 $1))) (msort (collapse (get-atoms &wuspace))))
!(assertPeTTaTest (msort (collapse (match &wuspace $1 (wu $1)))) ((wu (wu)) (wu (wu 42))))
