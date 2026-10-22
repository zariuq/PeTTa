(: rect (-> Number Number Shape))
(: &typed (SpaceOf (box Shape)))
!(let $v (rect 1 $x) (add-atom &typed (box $v)))
!(collapse (match &typed (box (rect 1 "s")) found))
