;A function reached only at runtime - picked from a space, passed as a closure -
;is checked by its declarations as a direct call is: with several declarations,
;those its arguments fit admit the call, and the result must fit one of them.
(: ovl (-> Number Number))
(: ovl (-> String String))
(= (ovl $x) $x)
!(bind! &fns (new-space))
!(add-atom &fns ovl)
!(test (let $f (match &fns $f $f) ($f 1)) 1)
!(test (let $f (match &fns $f $f) ($f "a")) "a")

;A closure's result is checked where its arrow type is demanded:
(: twice (-> (-> Number Number) Number Number))
(= (twice $f $x) ($f ($f $x)))
(: inc (-> Number Number))
(= (inc $x) (+ $x 1))
!(test (twice inc 1) 3)
