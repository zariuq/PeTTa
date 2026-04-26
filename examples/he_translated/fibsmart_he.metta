; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/fibsmart.metta

(= (fib-tr $n $a $b) (if (== $n 0) $a (fib-tr (- $n 1) $b (+ $a $b))))
(= (fib $n) (fib-tr $n 0 1))
!(assertPeTTaTest (fib 100) 354224848179261915075)
