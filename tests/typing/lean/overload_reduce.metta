(: poly (-> $a $a $a))
(: poly (-> Bool Bool Bool))
(= (poly $x $y) $x)
!(reduce (poly 1 "s"))
