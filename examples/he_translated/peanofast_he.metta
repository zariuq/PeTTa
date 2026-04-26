; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/peanofast.metta

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (expandK $expression $n) (if (== $n 0) done (let $temp1 (add-atom &self (num $expression)) (expandK (S $expression) (- $n 1)))))
(= (demo-peano $K) (expandK Z $K))
!(demo-peano 2500)
!(assertPeTTaTest (let $__tr_tuple_1 (collapse (match &self (num $1) $1)) (size-atom $__tr_tuple_1)) 2500)
