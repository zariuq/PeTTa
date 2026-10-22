(: superpose (-> (List Number) Number))
(= (invoke $f)
   (if True
       (let $x ($f ((progn (println! left) 1)
                    (progn (println! right) 2)))
            (println! $x))
       ($f "bad")))
!(invoke superpose)
