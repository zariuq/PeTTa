(= (unknown-id $x) $x)
(= (bind-string $x) (let $x "bad" ok))
!(let $v (the (| (Number Number) (Bool Bool)) (unknown-id ($x $y)))
   (progn (bind-string $x) (the (| (Number Number) (Bool Bool)) $v)))
