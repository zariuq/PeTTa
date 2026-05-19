; Translated from PeTTa to HE (10 atoms)
; Source: examples/parse.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
!(test (parse "A") A)
!(test (parse "(R A B)") (R A B))
!(test (parse "(R A (S B C))") (R A (S B C)))
!(test (parse "(* 2 21)") (quoted-syntax (quote (* 2 21))))
!(test (parse "\"42\"") "42")
