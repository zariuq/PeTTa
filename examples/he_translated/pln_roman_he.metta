; Translated from PeTTa to HE (9 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/pln_roman.metta

!(import! &self ../../lib/lib_pln.metta)
(= (STV A) (stv 0.5 0.9))
(= (STV B) (stv 0.25 0.9))
(= (STV C) (stv 0.25 0.9))
(= (STV D) (stv 0.5 0.9))
(= (kb) ((Sentence ((Inheritance A B) (stv 0.25 0.9)) (1)) (Sentence ((Inheritance A C) (stv 0.25 0.9)) (2)) (Sentence ((Inheritance B D) (stv 0.5 0.9)) (3)) (Sentence ((Inheritance C D) (stv 0.5 0.9)) (4))))
!(assertPeTTaTest (PLN.Query (kb) (Inheritance A D)) ((stv 0.5 0.9473684210526316) (1 2 3 4)))
