; Reduced HE repro for the hyperpose once/cheap-vs-expensive path.
; The cheap branch should win quickly; repeated calls amplify any branch
; management or cleanup pathology.

(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

(= (run-hyperpose-once)
   (once (hyperpose ((prime? 535372570000000063)
                     (prime? 5421844300001)))))

(= (repeat-hyperpose 0) done)
(= (repeat-hyperpose $n)
   (let $_ (run-hyperpose-once)
        (repeat-hyperpose (- $n 1))))

!(repeat-hyperpose 3)
