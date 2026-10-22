(: hold-first (-> Number Atom Number Atom))
(= (hold-first $bound $x $unused) $x)
(= (invoke $f)
   (if True
       ($f (progn (println! effect) 3) 1)
       ($f unused "bad")))
!(invoke (hold-first 0))
