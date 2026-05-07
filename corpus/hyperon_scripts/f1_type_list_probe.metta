!(import! &m f1_moduleA)
!(let $x (collapse (get-atoms &m)) (get-type $x))
!(let $x (collapse (get-atoms &m)) (get-metatype $x))
