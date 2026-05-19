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
!(test (forall (f) P) false)
!(test (forall (g $x) P) false)
!(test (let $genlambda (|-> ($x) (g $x)) (forall ($genlambda $z) P)) false)
!(test (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(test (let $checklambda (|-> ($v) (< $v 2)) (forall (g 1) $checklambda)) true)
!(test (let $checklambda (|-> ($v) (< $v 2)) (forall (g 2) $checklambda)) false)
!(test (let* (($checklambda (|-> ($v) (< $v 2))) ($genlambda (|-> ($x) (g $x)))) (forall ($genlambda $z) $checklambda)) false)
!(test (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 2))) false)
!(test (forall ((|-> ($x) (g $x)) $z) (|-> ($v) (< $v 20))) true)
!(test (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 2)) 42)) false)
!(test (forall ((|-> ($x) (g $x)) $z) (if True (|-> ($v) (< $v 20)) 42)) true)
!(test (forall ((|-> ($x) (* 100 (g $x))) $z) (if True (|-> ($v) (< $v 20)) 42)) false)
