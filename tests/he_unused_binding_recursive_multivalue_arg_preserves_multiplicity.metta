(= (countdown $n)
   (if (== $n 0)
       done
       (countdown (- $n 1))))

!(test
  (assertEqual (collapse (let $ignored (countdown (superpose (1 2))) 42))
               (42 42))
  ())
