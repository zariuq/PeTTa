; Reduced HE witness for the translated matespace2 rewrite path.
; This preserves the superpose/collapse/state interaction of the full example
; while keeping the search small enough to certify semantics directly.

(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand)
   (case (superpose (collapse (match &self (num $t) $t)))
         (($t ((add-atom-no-duplicate &self (num (M $t)))
               (add-atom-no-duplicate &self (num (W $t))))))))

(= (mate)
   (case (superpose (collapse (match &self (num (M $t)) $t)))
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (add-atom-no-duplicate &self (num (C $t))))))))))

(= (rewriteK $n)
   (if (== $n 0)
       done
       (let* (($temp1 (expand))
              ($temp2 (mate)))
             (rewriteK (- $n 1)))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (rewriteK $K)))
         (match &self (num $1) (num $1))))

!(assertEqualToEval
  (let $tuple (collapse (mate-space-demo 4))
       (size-atom $tuple))
  2873)
