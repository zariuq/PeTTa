;A type variable inside a structured parameter type names an unknown part of
;it (a parameter whose whole type is a variable is parametric instead, see
;fail_nonparametric_param):
(: first-of (-> ($a $b) Number))
(= (first-of ($x $y)) (+ $x 1))
!(test (first-of (1 2)) 2)

;An argument's runtime check tests its declared type's known part; a variable
;another argument instantiated does not decide it:
(: push (-> (List $a) $a (List $a)))
(= (push $xs $x) (cons $x $xs))
(: mixed (-> Expression))
(= (mixed) (1 "a"))
!(test (push (mixed) 2) (2 1 "a"))
