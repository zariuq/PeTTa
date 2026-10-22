(: keep (-> Atom Number %Undefined%))
(= (keep $x $n) (data $x $n))
(= (apply-one $f $x) ($f $x))
!(test (apply-one (keep (quote held)) 2) (data (quote held) 2))
