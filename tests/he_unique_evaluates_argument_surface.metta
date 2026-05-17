(= (? $term)
   (collapse
     (unique
       ($term
        (chain (unquote (quote $term)) $_
          done)))))

(= (fact a) tv)

!(assertEqualToEval
  (? (fact a))
  (((fact a) done)))
