; List-headed tuple expressions whose head evaluates to a non-callable value
; must evaluate both branches exactly once under --he.

(= (tick-inline $x)
   (let $_ (add-atom &self (seen-inline $x))
        done))

(= (tick-fun $x)
   (let $_ (add-atom &self (seen-fun $x))
        done))

(= (pair-effects $left $right)
   ((tick-fun $left)
    (tick-fun $right)))

!(assertEqualToEval
  (let* (($seed (add-atom &self (seen-inline rootinline)))
         ($_ ((tick-inline leftinline) (tick-inline rightinline))))
    (length (collapse (match &self (seen-inline $xinline) (seen-inline $xinline)))))
  3)

!(assertEqualToEval
  (let* (($seed (add-atom &self (seen-fun rootfun)))
         ($_ (pair-effects leftfun rightfun)))
    (length (collapse (match &self (seen-fun $xfun) (seen-fun $xfun)))))
  3)
