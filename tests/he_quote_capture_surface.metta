; PeTTa --he preserves source quote semantics: quote returns syntax data,
; not an extra (quote ...) wrapper value.
!(assertEqualToResult (quote (+ 1 2)) ((+ 1 2)))
!(assertEqualToResult (quote (quote (+ 1 2))) ((quote (+ 1 2))))

(= (id2 $x) $x)
!(assertEqualToResult (capture (id2 7)) (7))
!(assertEqualToResult (capture quote) (quote))
!(assertEqualToResult (capture (quote (+ 1 2))) ((+ 1 2)))
!(assertEqualToResult (let $f capture $f) (capture))
!(assertEqualToResult (let $f capture ($f (id2 8))) (8))
!(assertEqualToResult (let $f capture ($f (quote (+ 1 2)))) ((+ 1 2)))
