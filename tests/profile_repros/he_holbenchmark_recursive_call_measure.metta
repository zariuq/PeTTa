; Reduced HE witness for deterministic recursive compiled-call evaluation.
; This isolates the apply-many/poly family from the broader holbenchmark
; suite so the next runtime tranche can focus on direct recursive call costs
; rather than match/collapse or list-fold surfaces.

(= (apply-many $f $n $x)
   (if (== $n 0) $x
       (apply-many $f (- $n 1) ($f $x))))

!(test (apply-many (+ 1) 5000 0)
       5000)

(= (poly $f $n)
   (if (== $n 0) 0
       (+ ($f $n) (poly $f (- $n 1)))))

!(test (poly (+ 1) 5000)
       12507500)
