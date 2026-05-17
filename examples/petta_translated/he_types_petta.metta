; Translated from HE to PeTTa (16 atoms)
; Source: examples/he_types.metta

!(import! &self ../../lib/lib_he.metta)
!(test (is-function (-> Atom Atom)) True)
!(test (is-function Atom) False)
!(test (match-types Atom Atom "Matched!" "Didn't match") "Matched!")
!(test (match-types Atom Number "Matched!" "Didn't match") "Matched!")
!(test (first-from-pair (A B)) A)
!(test (second-from-pair (A B)) B)
!(test (match-type-or True Number Bool) True)
