; Translated from PeTTa to HE (10 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/parse.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (parse "A") A)
!(assertPeTTaTest (parse "(R A B)") (R A B))
!(assertPeTTaTest (parse "(R A (S B C))") (R A (S B C)))
!(assertPeTTaTest (parse "(* 2 21)") (quote (* 2 21)))
!(assertPeTTaTest (parse "\"42\"") "42")
