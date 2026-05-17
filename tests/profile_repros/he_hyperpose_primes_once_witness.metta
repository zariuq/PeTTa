; Reduced HE witness for the hyperpose once/cheap-vs-expensive path.
; If HE semantics are healthy here, the cheap branch should satisfy `once`
; quickly even with one competing expensive branch.

(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

!(assertEqualToEval
  (once (hyperpose ((prime? 535372570000000063)
                    (prime? 5421844300001))))
  True)
