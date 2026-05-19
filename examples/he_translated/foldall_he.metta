; Translated from PeTTa to HE (25 atoms)
; Source: examples/foldall.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f) 2)
(= (f) 3)
(= (g 1) 2)
(= (g 2) 3)
(= (merge $A $B) (+ $A $B))
!(test (let $__tr_collapsed_1 (collapse (f)) (foldl-atom $__tr_collapsed_1 0 $__tr_acc_2 $__tr_item_3 (eval (merge $__tr_acc_2 $__tr_item_3)))) 5)
!(test (let $__tr_collapsed_4 (collapse (g $x)) (foldl-atom $__tr_collapsed_4 0 $__tr_acc_5 $__tr_item_6 (eval (merge $__tr_acc_5 $__tr_item_6)))) 5)
!(test (let $agglambda (|-> ($x $y) (+ $x $y)) (let $__tr_collapsed_7 (collapse (f)) (foldl-atom $__tr_collapsed_7 0 $__tr_acc_8 $__tr_item_9 (eval ($agglambda $__tr_acc_8 $__tr_item_9))))) 5)
!(test (let $agglambda (|-> ($x $y) (+ $x $y)) (let $__tr_collapsed_10 (collapse (g $z)) (foldl-atom $__tr_collapsed_10 0 $__tr_acc_11 $__tr_item_12 (eval ($agglambda $__tr_acc_11 $__tr_item_12))))) 5)
!(test (let $agglambda (|-> ($x $y) (+ $x $y)) (let $__tr_collapsed_13 (collapse (g $z)) (foldl-atom $__tr_collapsed_13 0 $__tr_acc_14 $__tr_item_15 (eval ($agglambda $__tr_acc_14 $__tr_item_15))))) 5)
!(test (let* (($agglambda (|-> ($x $y) (+ $x $y))) ($genlambda (|-> ($z) (f)))) (let $__tr_collapsed_16 (collapse ($genlambda $x)) (foldl-atom $__tr_collapsed_16 0 $__tr_acc_17 $__tr_item_18 (eval ($agglambda $__tr_acc_17 $__tr_item_18))))) 5)
!(test (let* (($agglambda (|-> ($x $y) (+ $x $y))) ($genlambda (|-> ($z) (g $z)))) (let $__tr_collapsed_19 (collapse ($genlambda $x)) (foldl-atom $__tr_collapsed_19 0 $__tr_acc_20 $__tr_item_21 (eval ($agglambda $__tr_acc_20 $__tr_item_21))))) 5)
!(test (let $__tr_collapsed_22 (collapse ((|-> ($z) (g $z)) $w)) (foldl-atom $__tr_collapsed_22 0 $__tr_acc_23 $__tr_item_24 (eval ((|-> ($x $y) (+ $x $y)) $__tr_acc_23 $__tr_item_24)))) 5)
!(test (let $__tr_collapsed_25 (collapse ((|-> ($z) (g $z)) $w)) (foldl-atom $__tr_collapsed_25 0 $__tr_acc_26 $__tr_item_27 (eval ((if True (let $f (|-> ($x $y) (+ $x $y)) $f) (empty)) $__tr_acc_26 $__tr_item_27)))) 5)
!(test (let $__tr_collapsed_28 (collapse ((|-> ($z) (* 2 (g $z))) $w)) (foldl-atom $__tr_collapsed_28 0 $__tr_acc_29 $__tr_item_30 (eval ((if True (let $f (|-> ($x $y) (+ $x $y)) $f) (empty)) $__tr_acc_29 $__tr_item_30)))) 10)
