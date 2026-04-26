; Translated from PeTTa to HE (14 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/callquoteevalreduce2.metta

(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))
(= (myfunc) 5)
(= (call-fib) (call (fib (myfunc))))
(= (quote-fib) (quote (fib (myfunc))))
(= (eval-fib) (eval (fib (myfunc))))
(= (reduce-fib) (eval (fib (myfunc))))
!(assertPeTTaTest (fib-call (call-fib)) (fib-call 5))
!(assertPeTTaTest (fib-quote (quote-fib)) (fib-quote (quote (fib (myfunc)))))
!(assertPeTTaTest (fib-eval (eval-fib)) (fib-eval 5))
!(assertPeTTaTest (fib-reduce (reduce-fib)) (fib-reduce 5))
