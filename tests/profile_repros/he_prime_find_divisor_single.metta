; Reduced HE repro for the single-thread prime?/find-divisor arithmetic lane.
; This uses a smaller prime many times at top level so SWI's profiler captures
; the arithmetic lane itself rather than startup/autoload noise or synthetic
; recursion scaffolding.

(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
!(prime? 5421847)
