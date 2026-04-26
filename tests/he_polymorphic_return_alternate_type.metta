(: at A)
(: at T)
(: t T)
(: testf (-> $a $a))
(= (testf at) t)

!(assertPeTTaTest (testf at) t)
