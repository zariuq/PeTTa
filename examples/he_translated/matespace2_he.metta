; Translated from PeTTa to HE (7 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/matespace2.metta

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (add-atom-no-duplicate $Space $Atom) (if (== () (collapse (once (match $Space $Atom $Atom)))) (add-atom $Space $Atom) (empty)))
(= (expand) (case (superpose (collapse (match &self (num $t) $t))) (($t ((add-atom-no-duplicate &self (num (M $t))) (add-atom-no-duplicate &self (num (W $t))))))))
(= (mate) (case (superpose (collapse (match &self (num (M $t)) $t))) (($t (case (once (match &self (num (W $t)) $t)) (($t (add-atom-no-duplicate &self (num (C $t))))))))))
(= (rewriteK $n) (if (== $n 0) done (let* (($temp1 (expand)) ($temp2 (mate))) (rewriteK (- $n 1)))))
(= (mate-space-demo $K) (let* (($s (add-atom &self (num Z))) ($g (rewriteK $K))) (match &self (num $1) (num $1))))
!(assertPeTTaTest (let $__tr_tuple_1 (collapse (mate-space-demo 80)) (size-atom $__tr_tuple_1)) 1297533)
