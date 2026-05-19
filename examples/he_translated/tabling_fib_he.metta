; Translated from PeTTa to HE (7 atoms)
; Source: examples/tabling_fib.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self (library lib_tabling))
!(tabled (fib $N))
(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))
!(test (fib 30) 832040)
