(= (mk $x) (box $x))
(= (inc $x) (+ $x 1))
(= (unb $f (mk $a)) ($f $a))
!(unb inc (box 4))
