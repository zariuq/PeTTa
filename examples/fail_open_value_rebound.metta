;A check of an unbound value holds it to the type: binding it to a string
;after it passed as a Number is a type error at the binding.
(: number-id (-> Number Number))
(= (number-id $x) $x)
(= (bind-string $x) (let $x "bad" ok))
!(let $r (number-id $x) (let $u (bind-string $x) (the Number $r)))
