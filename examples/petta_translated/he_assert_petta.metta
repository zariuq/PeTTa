; Translated from HE to PeTTa (8 atoms)
; Source: examples/he_assert.metta

!(import! &self ../../lib/lib_he.metta)
!(test (assertEqual (+ 1 2) (- 6 3)) ())
!(test (assertAlphaEqual (h $x $y) (h $a $b)) ())
!(test (assertAlphaEqual (quote (+ $x $y)) (quote (+ $a $b))) ())
