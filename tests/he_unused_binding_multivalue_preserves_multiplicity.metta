(= (emit-many)
   (superpose (a b)))

!(test
  (assertEqual (collapse (let $ignored (emit-many) 42))
               (42 42))
  ())
