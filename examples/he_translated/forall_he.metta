; Translated from PeTTa to HE (29 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/forall.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) 1)
(= (f) 2)
(= (g 1) 1)
(= (g 2) 2)
(= (P $X) (< $X 2))
!(assertPeTTaTest (forall (f) P) false)
!(assertPeTTaTest (forall (g $x) P) false)
!(assertPeTTaTest (let $genlambda (|-> ($x) (g $x)) (forall ($genlambda $z) P)) false)
!(assertPeTTaTest (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(assertPeTTaTest (let $checklambda (|-> ($v) (< $v 2)) (forall (g 1) $checklambda)) true)
!(assertPeTTaTest (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(assertPeTTaTest (let* (($checklambda (|-> ($v) (< $v 2))) ($genlambda (|-> ($x) (g $x)))) (forall ($genlambda $z) $checklambda)) false)
!(assertPeTTaTest (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 2))) false)
!(assertPeTTaTest (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 20))) true)
!(assertPeTTaTest (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 2)) 42)) false)
!(assertPeTTaTest (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 20)) 42)) true)
!(assertPeTTaTest (forall ((|-> ($x) (* 100 (g $x))) $z) (if True (|-> ($v) (< $v 20)) 42)) false)
