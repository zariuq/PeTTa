; Translated from PeTTa to HE (10 atoms)
; Source: examples/parse.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
!(assertEqualToEval (parse "A") A)
!(assertEqualToEval (parse "(R A B)") (R A B))
!(assertEqualToEval (parse "(R A (S B C))") (R A (S B C)))
!(assertEqualToEval (parse "(* 2 21)") (quoted-syntax (quote (* 2 21))))
!(assertEqualToEval (parse "\"42\"") "42")
