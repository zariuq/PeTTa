; Reduced HE witness for the translated peano expansion path.
; This keeps the translated state/match recursion shape while bounding the
; workload so correctness can be certified separately from scale.

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

!(assertPeTTaTest
  (let $__tr_tuple_1 (collapse (demo-peano 50))
       (size-atom $__tr_tuple_1))
  51)
