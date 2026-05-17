(= (peano-add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (peano-expand-once)
   (case (match &self (num $t) $t)
         (($x (peano-add-atom-no-duplicate &self (num (S $x)))))))

(= (peano-expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (peano-expand-once)
            (peano-expandK (- $n 1)))))

(= (peano-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (peano-expandK $K)))
         (match &self (num $1) $1)))

!(assertEqualToEval
  (let $tuple (collapse (peano-demo 300))
       (size-atom $tuple))
  301)
