;Only (brand Meters E) makes a Meters: a plain number is not one.
(: Meters (Newtype Number))
(: add-m (-> Meters Meters Meters))
(= (add-m $a $b) (brand Meters (+ $a $b)))
!(add-m 2 3)
