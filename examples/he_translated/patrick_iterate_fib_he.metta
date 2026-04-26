; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/patrick_iterate_fib.metta

!(import! &self (library lib_patrick))
(= (fib-step $i ($a $b)) ($b (+ $a $b)))
(= (fib $n) (first (iterate 0 $n (0 1) fib-step)))
!(assertPeTTaTest (fib 100) 354224848179261915075)
