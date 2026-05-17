!(import! &self (library lib_patrick))

(= (quad-step-small $dummy ($t $i $sum))
   (if (== $i $t)
       ((+ $t 1) 1 (+ $sum (* $t $i)))
       ($t (+ $i 1) (+ $sum (* $t $i)))))

!(assertEqualToEval
  (last (iterate 0 3 (1 1 0) quad-step-small))
  7)
