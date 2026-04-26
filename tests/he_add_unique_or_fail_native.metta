!(import! &self ../lib/lib_datastructures.metta)

!(bind! &dup (new-space))
!(add-unique-or-fail &dup (a b))
!(add-unique-or-fail &dup (a b))
!(assertEqual (size &dup) 1)
!(assertEqual (collapse (match &dup $x $x)) ((s [a,b])))
