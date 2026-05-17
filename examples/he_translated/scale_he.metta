; Translated from PeTTa to HE (9 atoms)
; Source: examples/scale.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (length $expr) (let $tuple (eval $expr) (size-atom $tuple)))
(= (addK $K) (if (== $K 0) done (let* (($K10 (% $K 10)) ($t (add-atom &self (r $K $K10)))) (addK (- $K 1)))))
(= (q-all) (collapse (match &self (r $x $y) (r $x $y))))
(= (q-first $a) (collapse (match &self (r $a $y) (r $a $y))))
(= (q-second $b) (collapse (match &self (r $x $b) (r $x $b))))
(= (q-both $a $b) (collapse (match &self (r $a $b) (r $a $b))))
(= (q-rel $r) (collapse (match &self ($r 643 3) ($r 643 3))))
(= (indexing-demo $K) (let* (($temp (addK $K)) ($all (q-all)) ($first (q-first 7)) ($second (q-second 3)) ($rel (q-rel r)) ($both (q-both 42 2))) (all: (length $all) first: (length $first) second: (length $second) rel: (length $rel) both: (length $both))))
!(assertEqualToEval (indexing-demo 1000000) (all: 1000000 first: 1 second: 100000 rel: 1 both: 1))
