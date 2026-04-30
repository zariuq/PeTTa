; Guard the HE lowering boundary where == compares against nested callable
; arithmetic/recursion results. This was the hotspot behind the direct
; hyperpose_primes slowdown, but the core issue is callable lowering inside
; equality, not hyperpose itself.

(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

!(assertPeTTaTest
  (prime? 5421844300001)
  True)
