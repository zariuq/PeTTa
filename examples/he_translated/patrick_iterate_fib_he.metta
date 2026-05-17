; Translated from PeTTa to HE (6 atoms)
; Source: examples/patrick_iterate_fib.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self (library lib_patrick))
(= (fib-step $i ($a $b)) ($b (+ $a $b)))
(= (fib $n) (first (iterate 0 $n (0 1) fib-step)))
!(assertEqualToEval (fib 100) 354224848179261915075)
