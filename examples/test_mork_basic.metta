; Test basic MORK space operations

!(import! &self ../lib/lib_he)

; Add atoms
!(add-atom &mork (fact a))
!(add-atom &mork (fact b))
!(add-atom &mork (fact c))

; Test match
!(test (collapse (match &mork (fact $x) $x))
       (a b c))

; Remove one
!(remove-atom &mork (fact b))

; Test match after removal
!(test (collapse (match &mork (fact $x) $x))
       (a c))
