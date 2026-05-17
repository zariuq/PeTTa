; Translated from HE to PeTTa (11 atoms)
; Source: examples/he_equalreduct.metta

!(import! &self ../../lib/lib_he.metta)
(= (add 1 2) 3)
!(test (id 5) 5)
!(test (=alpha (Father $X) (Father $Y)) True)
!(test (=alpha (Father $X) (Son $X)) False)
!(test (if-equal 1 1 "Equal" "Not Equal") "Equal")
