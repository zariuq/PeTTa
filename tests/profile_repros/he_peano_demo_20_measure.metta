; Smaller HE witness for the translated peano expansion path.
; This preserves the same match/expand/count shape as the 50-step witness,
; but gives a faster loop for replay-focused profiling iterations.

(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand-once)
   (case (match &self (num $t) $t)
         (($x (add-atom-no-duplicate &self (num (S $x)))))))

(= (expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (expand-once)
            (expandK (- $n 1)))))

(= (demo-peano $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (expandK $K)))
         (match &self (num $1) $1)))

!(let $__tr_tuple_1 (collapse (demo-peano 20))
     (size-atom $__tr_tuple_1))
