(= (loop $n $acc)
   (if (== $n 0) $acc (loop (- $n 1) (+ $acc $n))))
!(loop 10 0)
