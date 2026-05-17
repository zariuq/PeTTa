!(assertEqualToEval (+ 1 2) 3)

(= (two-results) 3)
(= (two-results) 2)
(= (tuple-result) (3 2))

!(assertEqualToEval (two-results) (3 2))
!(assertEqualToEval (tuple-result) (3 2))

(= (quoted-syntax (quote $expr)) $expr)
(= (quote-demo) (quote-before (quoted-syntax (quote (fib 5)))))
!(assertEqualToEval (quote-demo) (quote-before (quoted-syntax (quote (fib 5)))))
