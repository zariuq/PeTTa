!(bind! &probe (new-space))

(= (missing-probe $space $atom)
   (== () (collapse (once (match $space $atom $atom)))))

!(assertEqual (missing-probe &probe foo) true)
!(assertEqual (add-atom &probe foo) ())
!(assertEqual (missing-probe &probe foo) false)
!(assertEqual (missing-probe &probe (pair a b)) true)
!(assertEqual (add-atom &probe (pair a b)) ())
!(assertEqual (missing-probe &probe (pair a b)) false)
