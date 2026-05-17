!(import! &self (library lib_roman))

!(assertEqual (map-flat (+ 1) (1 2 3)) (2 3 4))
