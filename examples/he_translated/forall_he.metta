; Translated from PeTTa to HE (29 atoms)
; Source: examples/forall.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) 1)
(= (f) 2)
(= (g 1) 1)
(= (g 2) 2)
(= (P $X) (< $X 2))
!(assertEqualToEval (forall (f) P) false)
!(assertEqualToEval (forall (g $x) P) false)
!(assertEqualToEval (let $genlambda (|-> ($x) (g $x)) (forall ($genlambda $z) P)) false)
!(assertEqualToEval (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(assertEqualToEval (let $checklambda (|-> ($v) (< $v 2)) (forall (g 1) $checklambda)) true)
!(assertEqualToEval (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(assertEqualToEval (let* (($checklambda (|-> ($v) (< $v 2))) ($genlambda (|-> ($x) (g $x)))) (forall ($genlambda $z) $checklambda)) false)
!(assertEqualToEval (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 2))) false)
!(assertEqualToEval (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 20))) true)
!(assertEqualToEval (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 2)) 42)) false)
!(assertEqualToEval (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 20)) 42)) true)
!(assertEqualToEval (forall ((|-> ($x) (* 100 (g $x))) $z) (if True (|-> ($v) (< $v 20)) 42)) false)
