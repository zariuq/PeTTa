; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/tabling_fib.metta

!(import! &self (library lib_tabling))
!(tabled (fib $N))
(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))
!(assertPeTTaTest (fib 30) 832040)
