(: number-id (-> Number Number))
(= (number-id $x) $x)
!(let $v (number-id $x) (add-atom &self (= (captured) $v)))
!(let $v (captured) (let $v "s" $v))
