; Translated from HE to PeTTa (5 atoms)
; Source: examples/he_minimalmetta.metta

!(import! &self ../../lib/lib_he.metta)
(= (div $x $y $accum) (let $r1 (eval (- $x $y)) (let $r2 (eval (< $r1 0)) (let $r3 (unify $r2 True $accum (let $inc (eval (+ 1 $accum)) (let $r4 (eval (div $r1 $y $inc)) $r4))) $r3))))
!(test (let $rr (eval (div 350000 5 0)) $rr) 70000)
