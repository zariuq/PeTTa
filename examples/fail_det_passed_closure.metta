;A function passed where a det function is required must be det: two-ways
;gives two answers, so passing it to apply-det breaks apply-det's grade.
!(import! &self (library lib_det))
(: apply-det (-[det]-> (-[det]-> Number Number) Number Number))
(= (apply-det $f $x) ($f $x))
(: two-ways (-[nondet]-> Number Number))
(= (two-ways $x) (superpose ($x (+ $x 1))))
(: use (-[det]-> Number Number))
(= (use $x) (apply-det two-ways $x))
!(use 1)
