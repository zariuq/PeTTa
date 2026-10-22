!(import! &self (library lib_det))
(: bad-choose (-[det]-> Number Number))
(= (bad-choose $x)
   (superpose ($x (+ $x 1))))
