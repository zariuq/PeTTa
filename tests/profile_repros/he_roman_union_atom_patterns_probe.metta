; Smaller roman_test slice focused on the union-atom reverse-pattern helpers.

!(import! &self ../../lib/lib_roman.metta)

!(println! "DEBUG: union-atom-patterns")
!(assertEqualToEval (let (mylast $x) (1 2 3) $x) 3)
!(assertEqualToEval (let (init $xs) (1 2 3) $xs) (1 2))
!(assertEqualToEval (let (rcons $xs $x) (1 2 3) ($xs $x)) ((1 2) 3))
