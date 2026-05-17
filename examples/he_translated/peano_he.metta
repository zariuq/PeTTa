; Translated from PeTTa to HE (6 atoms)
; Source: examples/peano.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (add-atom-no-duplicate $Space $Atom) (if (== () (collapse (once (match $Space $Atom $Atom)))) (add-atom $Space $Atom) (empty)))
(= (expand-once) (case (match &self (num $t) $t) (($x (add-atom-no-duplicate &self (num (S $x)))))))
(= (expandK $n) (if (== $n 0) done (let $temp1 (expand-once) (expandK (- $n 1)))))
(= (demo-peano $K) (let* (($s (add-atom &self (num Z))) ($g (expandK $K))) (match &self (num $1) $1)))
!(assertEqualToEval (let $__tr_tuple_1 (collapse (demo-peano 300)) (size-atom $__tr_tuple_1)) 301)
