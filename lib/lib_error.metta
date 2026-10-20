(: if-error (-[det]-> $value $then $else (| $then $else)))
(= (if-error $value $then $else)
   (if (= $value (cons Error $_)) $then $else))
