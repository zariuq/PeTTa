(= (bad-base $x $y) "bad")
(: curried (-> Number (-> Number Number)))
(= (curried $x) (bad-base $x))
!(curried 1 2)
