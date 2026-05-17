(= (ms2-add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (ms2-expand)
   (case (superpose (collapse (match &self (num $t) $t)))
         (($t ((ms2-add-atom-no-duplicate &self (num (M $t)))
               (ms2-add-atom-no-duplicate &self (num (W $t))))))))

(= (ms2-mate)
   (case (superpose (collapse (match &self (num (M $t)) $t)))
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (ms2-add-atom-no-duplicate &self (num (C $t))))))))))

(= (ms2-rewriteK $n)
   (if (== $n 0)
       done
       (let* (($temp1 (ms2-expand))
              ($temp2 (ms2-mate)))
             (ms2-rewriteK (- $n 1)))))

(= (ms2-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (ms2-rewriteK $K)))
         (match &self (num $1) (num $1))))

!(assertEqualToEval
  (let $tuple (collapse (ms2-demo 4))
       (size-atom $tuple))
  2873)
