; Translated from PeTTa to HE (8 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/matchsingle.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(a b)
(a c)
(= (match-single-via-cut $space $pattern $outPattern) (let* (($x (match $space $pattern $outPattern)) ($temp (cut))) $x))
(= (match-single-via-once $space $pattern $outPattern) (once (match $space $pattern $outPattern)))
!(assertPeTTaTest (collapse (match-single-via-cut &self (a $x) (a $x))) ((a b)))
!(assertPeTTaTest (collapse (match-single-via-once &self (a $x) (a $x))) ((a b)))
