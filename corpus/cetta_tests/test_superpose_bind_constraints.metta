; CeTTa extension lane: public structural (Bindings ...) payloads are treated
; as user-facing values here even though the official HE spec only describes
; bindings semantically, not as a clearly standardized public concrete syntax.
(module-profile he_extended)

; Residual equality constraints should round-trip structurally through the
; CeTTa public collapse-bind / superpose-bind payload boundary.
!(assertEqualToResult
  (let $r ((token (Bindings () (((pair $x) (pair a))))))
    (collapse-bind (superpose-bind $r)))
  (((token (Bindings () (((pair $x) (pair a))))))))

; Assignment payloads and residual equalities should coexist faithfully.
!(assertEqualToResult
  (let $r ((token (Bindings ((x a)) (((pair $y) (pair b))))))
    (collapse-bind (superpose-bind $r)))
  (((token (Bindings ((x a)) (((pair $y) (pair b))))))))

; Fully ground contradictions should be rejected when restoring a payload.
!(assertEqualToResult
  (let $r ((token (Bindings () ((a b)))))
    (superpose-bind $r))
  ())
