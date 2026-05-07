; Strict HE lane: superpose-bind should consume payloads actually produced by
; collapse-bind in the same runtime.
!(assertEqualToResult
  (let $r (collapse-bind 1)
    (superpose-bind $r))
  (1))

(= marker a)

; The restored environment must thread into later tuple elements when the
; payload comes from an actual collapse-bind witness.
!(assertEqualToResult
  (let $r (collapse-bind ((match &self (= marker $x) $x) $x))
    ((superpose-bind $r) $x))
  (((a a) a)))
