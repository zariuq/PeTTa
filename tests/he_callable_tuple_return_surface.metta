; Returned tuples must evaluate callable subexpressions elementwise under --he,
; while genuine computed-head calls still keep their call semantics.

(= (returns-plus) (+))
(= (call-returned-plus) ((returns-plus) 1 1))
!(assertEqualToEval (call-returned-plus) 2)

(= (call-pair $f $x) (($f $x) ($f $x)))
!(assertEqualToEval (call-pair (+ 2) 1) (3 3))

!(import! &self ../lib/lib_roman)
!(assertEqualToEval (&&& (+ 2) (* 2) 1) (3 2))
