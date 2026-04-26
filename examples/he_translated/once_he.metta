; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/once.metta

(foo 1)
(foo 2)
(= (match-single $space $pat $ret) (once (match $space $pat $ret)))
!(let $x (match-single &self (foo $1) $1) (add-atom &self (bar $x)))
!(assertPeTTaTest (collapse (match &self (bar $1) (bar $1))) ((bar 1)))
