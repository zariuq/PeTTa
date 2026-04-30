; Translated from PeTTa to HE (8 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/foldallmatch.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(kb 1)
(kb 2)
!(assertPeTTaTest (let $__tr_collapsed_1 (collapse (match &self (kb $n) (+ $n 1))) (foldl-atom $__tr_collapsed_1 0 $__tr_acc_2 $__tr_item_3 (eval (+ $__tr_acc_2 $__tr_item_3)))) 5)
(= (f) 1)
(= (f) 2)
!(assertPeTTaTest (let $__tr_collapsed_4 (collapse (let $x (f) (+ 1 $x))) (foldl-atom $__tr_collapsed_4 0 $__tr_acc_5 $__tr_item_6 (eval (+ $__tr_acc_5 $__tr_item_6)))) 5)
