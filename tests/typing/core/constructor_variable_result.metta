(: odd-ctor (-> $a $a))
(: f (-> (List Number) (List Number)))
(= (f $x) $x)
!(f (odd-ctor (1 2)))
