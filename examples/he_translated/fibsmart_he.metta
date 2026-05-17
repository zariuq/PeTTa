; Translated from PeTTa to HE (4 atoms)
; Source: examples/fibsmart.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (fib-tr $n $a $b) (if (== $n 0) $a (fib-tr (- $n 1) $b (+ $a $b))))
(= (fib $n) (fib-tr $n 0 1))
!(assertEqualToEval (fib 100) 354224848179261915075)
