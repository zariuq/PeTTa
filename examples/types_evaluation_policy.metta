;Atom holds an argument or result unevaluated under -> only; under the other
;arrows it is any value:
(: hold (-> Atom Atom))
(= (hold $x) $x)
!(test (hold (+ 1 2)) (quote (+ 1 2)))
(: next (-[det]-> Number Atom))
(= (next $x) (+ $x 1))
!(test (next 1) 2)

;(once X) is X's first answer, also as a whole branch of superpose:
(= (alts) (superpose ((once (superpose (1 2))) 3 4)))
!(test (collapse (alts)) (1 3 4))

;A function whose declarations all commit commits to its first matching clause:
(: pick (-[det]-> Number Number))
(: pick (-[det]-> String String))
(= (pick $x) $x)
(= (pick $x) $x)
!(test (collapse (pick 1)) (1))
