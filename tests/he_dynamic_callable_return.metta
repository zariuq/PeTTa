(= (returns-plus) (+))
(= (compose $f $g $x) ($f ($g $x)))
(= (plus1-times2) (compose (* 2) (+ 1)))

!(assertPeTTaTest (returns-plus 1 1) 2)
!(assertPeTTaTest (plus1-times2 1) 4)
