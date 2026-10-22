;A value checked while unbound can be bound later to a value of its type, and
;the held check is no part of the value for =alpha or test.
(: number-id (-> Number Number))
(= (number-id $x) $x)
!(test (let $r (number-id $x) (let $x 5 $r)) 5)
!(test (let $r (number-id $y) (=alpha $r $z)) True)
