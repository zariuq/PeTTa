!(import! &self (library lib_roman))
;An Alias names a type:
(: Score (Alias Number))
(: double (-> Score Score))
(= (double $x) (* 2 $x))
!(test (double 3) 6)

;A Newtype is a type of its own, represented as another; (brand N E) makes its
;values, and brands are erased at runtime, in data and held arguments too:
(: Meters (Newtype Number))
(: meters (-> Number Meters))
(= (meters $x) (brand Meters $x))
(: add-m (-> Meters Meters Meters))
(= (add-m $a $b) (brand Meters (+ $a $b)))
!(test (add-m (meters 2) (meters 3)) 5)
!(test (cons (brand Meters 1) ()) (1))
(: keep (-> Atom Atom))
(= (keep $x) $x)
!(test (keep (brand Meters 4)) 4)

;A space declared (SpaceOf Row) lets its match patterns apply a det function,
;here lib_roman's as-pattern (@ $whole pattern):
(: &people (SpaceOf (Person Atom Number)))
!(bind! &people (new-space))
!(add-atom &people (Person ann 30))
!(test (collapse (match &people (@ $p (Person $n $a)) $p)) ((Person ann 30)))
