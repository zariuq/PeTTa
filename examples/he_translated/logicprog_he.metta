; Translated from PeTTa to HE (10 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/logicprog.metta

(= (successor b a) True)
(= (successor c b) True)
(= (successor d c) True)
(= (successor e d) True)
(= (successor f e) True)
(= (successor g f) True)
(= (later-in-alphabet $X $Y) (successor $X $Y))
(= (later-in-alphabet $X $Y) (and (successor $X $Z) (later-in-alphabet $Z $Y)))
!(assertPeTTaTest (collapse ((later-in-alphabet d $1) $1)) ((True c) (True b) (True a)))
