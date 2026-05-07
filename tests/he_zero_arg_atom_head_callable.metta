; Atom-head equations with zero arguments should evaluate in expression
; position under strict HE mode.

(: origin (-> Number))
(: call-origin (-> Number))
(: call-plus (-> Number Number))

(= origin 7)
(= call-origin origin)
(= (call-plus $x) (+ $x 1))

!(assertEqual call-origin 7)
!(assertEqual (call-plus 7) 8)
