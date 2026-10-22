;A closure checked only by its arity at the boundary has its result checked
;where it is used: bad returns a string where (-> Number Number) is demanded.
(= (bad $x) "oops")
(: run-typed (-> (-> Number Number) Number))
(= (run-typed $f) ($f 0))
!(bind! &callbacks (new-space))
!(add-atom &callbacks bad)
!(let $f (match &callbacks $name $name) (run-typed $f))
