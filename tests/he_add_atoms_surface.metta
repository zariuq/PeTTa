!(bind! &bag (new-space))
!(assertEqual (add-atoms &bag ((foo a) (foo b))) ())
!(assertEqualToResult (match &bag (foo $x) $x) (a b))
