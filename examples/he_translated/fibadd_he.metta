; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/fibadd.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(add-atom &self (= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2))))))
!(assertPeTTaTest (fib 30) 832040)
