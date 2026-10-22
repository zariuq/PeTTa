;A det function whose body surely gives two answers is a determinism error.
!(import! &self (library lib_det))
(: twice (-[det]-> Number Number))
(= (twice $x) (superpose ($x $x)))
!(twice 1)
