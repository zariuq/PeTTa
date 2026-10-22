!(import! &self (library lib_det))
(: f (-[det]-> Atom Atom))
(= (f $x) a)
(= (f $x) b)
