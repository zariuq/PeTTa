; Translated from HE to PeTTa (11 atoms)
; Source: examples/he_evaluation.metta

!(import! &self ../../lib/lib_he.metta)
(= (double $x) (+ $x $x))
!(test (eval (double 5)) 10)
!(test (evalc (+ 5 5) &self) 10)
!(test (let $x (+ 2 3) (* $x 2)) 10)
!(test (for-each-in-atom (1 3 5 62 2 5) println!) (true true true true true true))
