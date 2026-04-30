; Small canonical-HE regression extracted from corpus/hyperon_scripts/d5_auto_types.metta.
; With auto type checking enabled, == must report a typed error here rather
; than silently returning false.

!(pragma! type-check auto)

!(assertEqualToResult
   (== 5 "S")
  ((Error (== 5 "S") (BadArgType 2 Number String))))
