(: at A)
(: at T)
(: t T)
(: testf (-> $a $a))
(= (testf at) t)

!(assertEqualToEval (testf at) t)
