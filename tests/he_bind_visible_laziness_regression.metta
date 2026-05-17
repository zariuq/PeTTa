; Characterize the bind-visible laziness contract.
; The outer `once` should observe only the first successful `let` branch and
; should not eagerly realize later branches before the first result is chosen.

(= (record-picked $x)
   (let $_ (add-atom &self (lazy-picked $x))
     ok))

(= (lazy-bind-pick)
   (once
     (let $x (superpose (1 2))
       (record-picked $x))))

!(assertEqualToEval (lazy-bind-pick) ok)
!(assertEqualToResult (collapse (match &self (lazy-picked $v) $v)) ((1)))
