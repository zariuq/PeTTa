; Translated from PeTTa to HE (10 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/parse.metta

!(assertPeTTaTest (parse "A") A)
!(assertPeTTaTest (parse "(R A B)") (R A B))
!(assertPeTTaTest (parse "(R A (S B C))") (R A (S B C)))
!(assertPeTTaTest (parse "(* 2 21)") (quote (* 2 21)))
!(assertPeTTaTest (parse "\"42\"") "42")
