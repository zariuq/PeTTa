; Translated from PeTTa to HE (14 atoms)
; Source: examples/callquoteevalreduce2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))
(= (myfunc) 5)
(= (call-fib) (call (fib (myfunc))))
(= (quote-fib) (quoted-syntax (quote (fib (myfunc)))))
(= (eval-fib) (unquote (quote (fib (myfunc)))))
(= (reduce-fib) (unquote (quote (fib (myfunc)))))
!(test (fib-call (call-fib)) (fib-call 5))
!(test (fib-quote (quote-fib)) (fib-quote (quoted-syntax (quote (fib (myfunc))))))
!(test (fib-eval (eval-fib)) (fib-eval 5))
!(test (fib-reduce (reduce-fib)) (fib-reduce 5))
