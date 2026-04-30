; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/fib.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (fib $N) (if (< $N 2) $N (+ (fib (- $N 1)) (fib (- $N 2)))))
!(assertPeTTaTest (fib 30) 832040)
