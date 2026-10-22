; A refinement (Refine Base Predicate) is the values of Base for which the pure
; Predicate gives True: EvenNumber without a get-type rule. The name stays
; closed, so conflicts with other types are still found at compile time, and
; it composes: (List EvenNumber) needs no rule of its own.
(: is-even (-> Number Bool))
(= (is-even $x) (== (% $x 2) 0))
(: EvenNumber (Refine Number is-even))

(: half (-> EvenNumber Number))
(= (half $x) (/ $x 2))
!(test (half 6) 3)

(: sum-evens (-> (List EvenNumber) Number))
(= (sum-evens ()) 0)
(= (sum-evens (cons $x $xs)) (+ $x (sum-evens $xs)))
!(test (sum-evens (2 4 6)) 12)

; An EvenNumber is a Number, so arithmetic needs no check:
(: double-even (-> EvenNumber Number))
(= (double-even $x) (* 2 $x))
!(test (double-even 4) 8)

; A refinement of a Newtype stays nominal:
(: Meters (Newtype Number))
(: is-positive (-> Meters Bool))
(= (is-positive $m) (> $m 0))
(: Distance (Refine Meters is-positive))
(: walk (-> Distance Meters))
(= (walk $d) $d)
!(test (walk (brand Meters 5)) 5)

; An open value checked as an EvenNumber is held to it:
!(test (let (Error $what $kind) (catch (let $x (the EvenNumber $y) (let $y 3 ok))) $kind)
       typecheck)
