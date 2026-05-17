!(import! &self ../lib/lib_roman)
!(assertEqualToEval (@ (1 2 3) (cons 1 (2 3))) (1 2 3))
