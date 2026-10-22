(= (unknown-id $x) $x)
(= (bind-string $x) (let $x "bad" ok))
!(let $v (the (List _) (unknown-id (cons 1 $tail)))
   (progn (bind-string $tail) (the (List Number) $v)))
