; Small canonical-HE regression extracted from corpus/hyperon_scripts/d2_higherfunc.metta.
; Full application of a curried higher-order helper must reduce, not stay data.

(: curry (-> (-> $a $b $c) (-> $a (-> $b $c))))
(= (((curry $f) $x) $y) ($f $x $y))

!(assertEqual
  (((curry +) 2) 3)
  5)
