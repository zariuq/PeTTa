; Small canonical-HE regression extracted from corpus/hyperon_scripts/d2_higherfunc.metta.
; Untyped zero-arg constructor tails must survive fmap recursion in HE mode.

(: curry-a (-> (-> $a $b $c) $a (-> $b $c)))
(= ((curry-a $f $a) $b) ($f $a $b))

(: fmap (-> (-> $a $b) ($F $a) ($F $b)))
(= (fmap $f ($C0))
  ($C0))
(= (fmap $f ($C $x))
  ($C ($f $x)))
(= (fmap $f ($C $x $xs))
  ($C ($f $x) (fmap $f $xs)))

!(assertEqual
  (fmap (curry-a + 2) (UntypedC 5 (UntypedC 8 (Null))))
  (UntypedC 7 (UntypedC 10 (Null))))
