; Translated from PeTTa to HE (17 atoms)
; Source: examples/callquoteevalreduce.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
(= (before-call) (call-before (call (fib 5))))
(= (before-quote) (quote-before (quoted-syntax (quote (fib 5)))))
(= (before-eval) (eval-before (unquote (quote (fib 5)))))
(= (before-reduce) (reduce-before (unquote (quote (fib 5)))))
(= (compilefib) (let $temp (add-atom &self (= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))) ((within (fib 5)) (call-within (call (fib 5))) (quote-within (quoted-syntax (quote (fib 5)))) (eval-within (unquote (quote (fib 5)))) (reduce-within (unquote (quote (fib 5)))))))
!(test (before-call-errors-ofc (before-quote) (before-eval) (before-reduce)) (before-call-errors-ofc (quote-before (quoted-syntax (quote (fib 5)))) (eval-before (quoted-syntax (quote (fib 5)))) (reduce-before (quoted-syntax (quote (fib 5))))))
!(test (compilefib) ((within (quoted-syntax (quote (fib 5)))) (call-within 5) (quote-within (quoted-syntax (quote (fib 5)))) (eval-within 5) (reduce-within 5)))
(= (after-call) (call-after (call (fib 5))))
(= (after-quote) (quote-after (quoted-syntax (quote (fib 5)))))
(= (after-eval) (eval-after (unquote (quote (fib 5)))))
(= (after-reduce) (reduce-after (unquote (quote (fib 5)))))
!(test ((before-call) (before-quote) (before-eval) (before-reduce)) ((call-before 5) (quote-before (quoted-syntax (quote (fib 5)))) (eval-before 5) (reduce-before 5)))
!(test ((after-call) (after-quote) (after-eval) (after-reduce)) ((call-after 5) (quote-after (quoted-syntax (quote (fib 5)))) (eval-after 5) (reduce-after 5)))
