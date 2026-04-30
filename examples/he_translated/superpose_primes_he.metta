; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/superpose_primes.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (find-divisor $n $test-divisor) (if (> (* $test-divisor $test-divisor) $n) $n (if (== 0 (% $n $test-divisor)) $test-divisor (find-divisor $n (+ $test-divisor 1)))))
(= (prime? $n) (== $n (find-divisor $n 2)))
!(assertPeTTaTest ((prime? 53537257) (prime? 53781811) (prime? 54218443) (prime? 54734431)) (True True True True))
