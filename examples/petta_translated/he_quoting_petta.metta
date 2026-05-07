; Translated from HE to PeTTa (14 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/he_quoting.metta

!(import! &self ../../lib/lib_he.metta)
!(test (quote (+ 1 2)) (quote (+ 1 2)))
!(test (eval (+ 1 2)) 3)
!(test (unquote (quote (+ 1 2))) 3)
!(test (repr (unquote 42)) "(unquote 42)")
!(test (noreduce-eq (+ 1 2) (+ 1 2)) True)
!(test (noreduce-eq (+ 1 2) 3) False)
