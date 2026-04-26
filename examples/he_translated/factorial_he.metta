; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/factorial.metta

(= (facF $n) (if (== $n 0) 1 (* $n (facF (- $n 1)))))
!(assertPeTTaTest (facF 10) 3628800)
