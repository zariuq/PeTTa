;An overloaded function picked at runtime keeps its contract: True fits
;neither declared result.
(: overloaded (-> Number Number))
(: overloaded (-> String String))
(= (overloaded $x) True)
!(bind! &callbacks (new-space))
!(add-atom &callbacks overloaded)
!(let $f (match &callbacks $name $name) ($f 1))
