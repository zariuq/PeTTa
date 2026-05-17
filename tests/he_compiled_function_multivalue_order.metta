!(bind! &scratch (new-space))

(= (emit-two)
   (superpose (a b)))

(= (use-space)
   (let $s (new-space)
     (let $u1 (add-atom $s (token a))
       (let $u2 (add-atom $s (token b))
         (get-atoms $s)))))

!(assertEqual (collapse (emit-two)) (a b))
!(assertEqual (collapse (use-space)) ((token a) (token b)))
