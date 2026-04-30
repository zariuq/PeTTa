; Translated from PeTTa to HE (17 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/callquoteevalreduce.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (before-call) (call-before (call (fib 5))))
(= (before-quote) (quote-before (quote (fib 5))))
(= (before-eval) (eval-before (eval (fib 5))))
(= (before-reduce) (reduce-before (eval (fib 5))))
(= (compilefib) (let $temp (add-atom &self (= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))) ((within (fib 5)) (call-within (call (fib 5))) (quote-within (quote (fib 5))) (eval-within (eval (fib 5))) (reduce-within (eval (fib 5))))))
!(assertPeTTaTest (before-call-errors-ofc (before-quote) (before-eval) (before-reduce)) (before-call-errors-ofc (quote-before (quote (fib 5))) (eval-before (quote (fib 5))) (reduce-before (quote (fib 5)))))
!(assertPeTTaTest (compilefib) ((within (quote (fib 5))) (call-within 5) (quote-within (quote (fib 5))) (eval-within 5) (reduce-within 5)))
(= (after-call) (call-after (call (fib 5))))
(= (after-quote) (quote-after (quote (fib 5))))
(= (after-eval) (eval-after (eval (fib 5))))
(= (after-reduce) (reduce-after (eval (fib 5))))
!(assertPeTTaTest ((before-call) (before-quote) (before-eval) (before-reduce)) ((call-before 5) (quote-before (quote (fib 5))) (eval-before 5) (reduce-before 5)))
!(assertPeTTaTest ((after-call) (after-quote) (after-eval) (after-reduce)) ((call-after 5) (quote-after (quote (fib 5))) (eval-after 5) (reduce-after 5)))
