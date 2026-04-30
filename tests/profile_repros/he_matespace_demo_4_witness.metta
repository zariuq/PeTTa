; Reduced HE witness for the translated matespace rewrite path.
; This keeps the stateful add/match semantics of the full example but uses a
; small K so correctness can be certified separately from the full workload.

(= (count-demo $expr)
   (let $tuple (eval $expr)
        (size-atom $tuple)))

(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand)
   (case (match &self (num $t) $t)
         (($t ((add-atom-no-duplicate &self (num (M $t)))
               (add-atom-no-duplicate &self (num (W $t))))))))

(= (mate)
   (case (match &self (num (M $t)) $t)
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (add-atom-no-duplicate &self (num (C $t))))))))))

(= (expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (expand)
            (expandK (- $n 1)))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (expandK $K))
          ($h (mate)))
         (match &self (num $1) (num $1))))

!(test
  (count-demo (collapse (mate-space-demo 4)))
  103)
