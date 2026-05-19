; Translated from PeTTa to HE (7 atoms)
; Source: examples/once.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(foo 1)
(foo 2)
(= (match-single $space $pat $ret) (once (match $space $pat $ret)))
!(let $x (match-single &self (foo $1) $1) (add-atom &self (bar $x)))
!(test (collapse (match &self (bar $1) (bar $1))) ((bar 1)))
