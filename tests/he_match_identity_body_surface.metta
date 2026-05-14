!(bind! &matchid (new-space))

!(assertEqual (add-atom &matchid (num 1)) ())
!(assertEqual (add-atom &matchid (num 2)) ())

!(assertEqual
  (let $vals (collapse (match &matchid (num $x) (num $x)))
    (size-atom $vals))
  2)

!(assertEqual
  (collapse (match &matchid (num $x) (+ $x 1)))
  (2 3))
