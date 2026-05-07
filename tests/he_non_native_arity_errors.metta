!(assertEqualToResult (eval) ((Error (eval) IncorrectNumberOfArguments)))
!(assertEqualToResult (import!) ((Error (import!) IncorrectNumberOfArguments)))
!(assertEqualToResult (get-metatype) ((Error (get-metatype) IncorrectNumberOfArguments)))

(: add2 (-> Number Number Number))
(= (add2 $x $y) (+ $x $y))
!(assertEqualToResult (add2 1) ((Error (add2 1) IncorrectNumberOfArguments)))

!(assertEqualToResult (sealed) ((Error (sealed) IncorrectNumberOfArguments)))
