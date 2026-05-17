(= (tick-fun $x) done)
(= (pair-effects $left $right) ((tick-fun $left) (tick-fun $right)))
