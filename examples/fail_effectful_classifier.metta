;get-type rules that may act are not used by type checks, so a check never
;acts: here a is no Custom by the declarations, and the call is a type error.
(= (get-type $v) (progn (println! checked) Custom))
(: use-custom (-> Custom Custom))
(= (use-custom $x) $x)
(= (unknown-id $x) $x)
!(use-custom (unknown-id a))
