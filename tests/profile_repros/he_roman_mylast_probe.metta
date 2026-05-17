; Smallest roman_test slice currently known for the union-atom reverse matcher.

!(import! &self ../../lib/lib_roman.metta)

!(println! "DEBUG: mylast")
!(assertEqualToEval (let (mylast $x) (1 2 3) $x) 3)
