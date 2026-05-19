; Translated from PeTTa to HE (4 atoms)
; Source: examples/matespacefast.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (rewriteK $t $n) (if (== $n 0) done (let* (($_1 (add-atom &self (num (M $t)))) ($_2 (add-atom &self (num (W $t)))) ($_3 (add-atom &self (num (C $t))))) ((rewriteK (M $t) (- $n 1)) (rewriteK (W $t) (- $n 1))))))
(= (mate-space-demo $K) (let* (($s (add-atom &self (num Z))) ($g (rewriteK Z $K))) (match &self (num $1) (num $1))))
!(test (let $__tr_tuple_1 (collapse (mate-space-demo 19)) (size-atom $__tr_tuple_1)) 1572862)
