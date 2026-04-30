; Reduced roman_test slice focused on the reverse-pattern helpers.

!(import! &self ../../lib/lib_roman.metta)

!(println! "DEBUG: reverse-patterns")
!(assertPeTTaTest (let (@ $lst (cons $h $t)) (1 2 3) ($lst $h $t)) ((1 2 3) 1 (2 3)))
!(assertPeTTaTest (let (head $x) (1 2 3) $x) 1)
!(assertPeTTaTest (let (tail $xs) (1 2 3) $xs) (2 3))
!(assertPeTTaTest (let (mylast $x) (1 2 3) $x) 3)
!(assertPeTTaTest (let (init $xs) (1 2 3) $xs) (1 2))
!(assertPeTTaTest (let (rcons $xs $x) (1 2 3) ($xs $x)) ((1 2) 3))
