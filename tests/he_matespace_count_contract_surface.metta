(= (ms-add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (ms-expand)
   (case (match &self (num $t) $t)
         (($t ((ms-add-atom-no-duplicate &self (num (M $t)))
               (ms-add-atom-no-duplicate &self (num (W $t))))))))

(= (ms-mate)
   (case (match &self (num (M $t)) $t)
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (ms-add-atom-no-duplicate &self (num (C $t))))))))))

(= (ms-expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (ms-expand)
            (ms-expandK (- $n 1)))))

(= (ms-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (ms-expandK $K))
          ($h (ms-mate)))
         (match &self (num $1) (num $1))))

!(assertEqualToEval
  (let $tuple (collapse (ms-demo 4))
       (size-atom $tuple))
  103)
