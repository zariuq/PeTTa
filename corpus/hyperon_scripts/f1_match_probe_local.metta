!(import! &m f1_moduleA)
!(match &m (= (f 2) $x) $x)
