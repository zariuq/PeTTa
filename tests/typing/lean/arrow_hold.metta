(: arrow-id (-> (-> Number Number) (-> Number Number)))
(= (arrow-id $x) $x)
(= (bind-string $x) (let $x "bad" ok))
!(let $r (arrow-id $x) (let $u (bind-string $x) (the (-> Number Number) $r)))
