(= (mark-expected $x)
   (let $_ (add-atom &self (expected-mark $x))
     $x))

!(assertEqualMsg 42 (mark-expected 42) "msg")
!(assertEqual (collapse (match &self (expected-mark $x) $x)) (42))
