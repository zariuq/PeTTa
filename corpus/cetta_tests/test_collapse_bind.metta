(module-profile he_extended)

; CeTTa extension lane: this file checks the public serialized Bindings payload
; shape, which is not clearly standardized by the official HE spec.
; Strict HE roundtrip coverage lives in test_superpose_bind_restore.metta.

; collapse-bind is deterministic and returns ONE packed expression whose items
; are (<atom> (Bindings ...)) pairs in CeTTa's public surface.
(= (multi) a)
(= (multi) b)
!(assertEqualToResult
  (collapse-bind (multi))
  (((a (Bindings () ())) (b (Bindings () ())))))

; Empty branches are internal no-result sentinels and must not be serialized
; into the packed collapse-bind payload.
!(assertEqualToResult
  (collapse-bind (let $x (superpose (a b)) (if (== $x a) (empty) $x)))
  (((b (Bindings ((x b)) ())))))
