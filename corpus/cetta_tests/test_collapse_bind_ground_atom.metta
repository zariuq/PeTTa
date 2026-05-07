(module-profile he_extended)

; CeTTa extension lane: this file checks the public serialized Bindings payload
; shape for collapse-bind on a ground atom. Strict HE roundtrip coverage lives
; in test_superpose_bind_restore.metta.

; collapse-bind packs a ground atom with an empty structural bindings payload.
!(assertEqualToResult
  (collapse-bind 1)
  (((1 (Bindings () ())))))
