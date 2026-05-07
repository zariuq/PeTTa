!(import! &m f1_moduleA)
!(let $x (match &m (= (f 2) $x) $x) (eval $x))
