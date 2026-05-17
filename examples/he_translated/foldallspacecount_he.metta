; Translated from PeTTa to HE (8 atoms)
; Source: examples/foldallspacecount.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(foo 1)
(foo 2)
(foo 3)
(= (countitem) (let $x (match &self (foo $1) (foo $1)) 1))
(= (merge $a $b) (+ $a $b))
(= (spacecount $x) (let $__tr_collapsed_1 (collapse (countitem)) (foldl-atom $__tr_collapsed_1 0 $__tr_acc_2 $__tr_item_3 (eval (merge $__tr_acc_2 $__tr_item_3)))))
!(assertEqualToEval (let $__tr_collapsed_4 (collapse (countitem)) (foldl-atom $__tr_collapsed_4 0 $__tr_acc_5 $__tr_item_6 (eval (merge $__tr_acc_5 $__tr_item_6)))) 3)
