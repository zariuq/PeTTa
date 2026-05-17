; Imported reverse-function helpers must stay usable as let-pattern heads under --he.

!(import! &self ../lib/lib_roman)

!(assertEqualToEval (@ (1 2 3) (cons 1 (2 3))) (1 2 3))
!(assertEqualToEval (let (@ $lst (cons $h $t)) (1 2 3) ($lst $h $t)) ((1 2 3) 1 (2 3)))
!(assertEqualToEval (let (head $x) (1 2 3) $x) 1)
!(assertEqualToEval (let (tail $xs) (1 2 3) $xs) (2 3))
!(assertEqualToEval (let (mylast $x) (1 2 3) $x) 3)
!(assertEqualToEval (let (init $xs) (1 2 3) $xs) (1 2))
!(assertEqualToEval (let (rcons $xs $x) (1 2 3) ($xs $x)) ((1 2) 3))
