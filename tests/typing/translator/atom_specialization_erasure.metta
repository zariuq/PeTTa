(: hold-first (-> Atom Number Atom))
(= (hold-first $x $unused) $x)
(= (invoke $f)
   (if True
       ($f (progn (println! effect) 3) 1)
       ($f unused "bad")))
!(invoke hold-first)
