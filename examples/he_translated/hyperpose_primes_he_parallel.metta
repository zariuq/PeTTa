; Translated from PeTTa to HE (preserve hyperpose, 8 atoms)
; Source: examples/hyperpose_primes.metta
; Translation target: PeTTa HE parallel
; Intended runtime: ./run.sh --he
; Portability: requires HE runtime with hyperpose support; not claimed portable Pure HE


(= (find-divisor $n $test-divisor) (if (> (* $test-divisor $test-divisor) $n) $n (if (== 0 (% $n $test-divisor)) $test-divisor (find-divisor $n (+ $test-divisor 1)))))
(= (prime? $n) (== $n (find-divisor $n 2)))
!(assertEqualToEval (msort (collapse (let $xs (3 1 2) (hyperpose $xs)))) (1 2 3))
!(assertEqualToEval (collapse (hyperpose ((prime? 5353725700019) (prime? 5378181100003) (prime? 5421844300001) (prime? 5473443100001)))) (True True True True))
!(assertEqualToEval (once (hyperpose ((prime? 535372570000000063) (prime? 537818110000000001) (prime? 5421844300001) (prime? 547344310000000013)))) True)
