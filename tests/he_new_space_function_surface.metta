(= (use-space-count)
   (let $s (new-space)
     (let $u1 (add-atom $s (token a))
       (let $u2 (add-atom $s (token b))
         (length (collapse (get-atoms $s)))))))

!(assertEqual (use-space-count) 2)
