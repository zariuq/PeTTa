; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/fibadd.metta

!(add-atom &self (= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2))))))
!(assertPeTTaTest (fib 30) 832040)
