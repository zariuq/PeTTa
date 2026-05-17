(= (mk-link (($LinkType $A $B) $T1)
            (($LinkType $B $C) $T2))
   (($LinkType $A $C) done))

!(assertEqualToEval
  (mk-link ((Inheritance a b) tv1)
           ((Inheritance b c) tv2))
  ((Inheritance a c) done))
