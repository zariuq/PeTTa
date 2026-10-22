(: number-id (-> Number Number))
(= (number-id $x) $x)
!(let $r (number-id $x) (=alpha $r $y))
