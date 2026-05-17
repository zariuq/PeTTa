!(import! &self ../lib/lib_he)

!(test (assertEqual (+ 1 2) (- 6 3)) ())
!(test (assertAlphaEqual (h $x $y) (h $a $b)) ())
!(test (assertAlphaEqual (quote (+ $x $y)) (quote (+ $a $b))) ())

; Additional assertion forms:
;!(assertEqualToResult (+ 1 2) 3)
;(= (adder) $x)
;!(assertAlphaEqualToResult (adder) ($y))
