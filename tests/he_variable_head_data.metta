; Unbound variable-headed expressions are data under --he; variables already
; bound to callables remain callable.

(= (return-second $x $y) $y)

!(assertAlphaEqualToResult (return-second guard ($x 3 4)) (($x 3 4)))
!(assertEqual (let $f + ($f 1 2)) 3)
