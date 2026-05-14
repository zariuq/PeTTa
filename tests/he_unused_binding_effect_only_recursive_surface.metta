(= (branchwalk $n)
   (if (== $n 0)
       done
       (let $ignored (add-atom &self (tick $n))
         ((branchwalk (- $n 1))
          (branchwalk (- $n 1))))))

!(test
  (let $ignored (branchwalk 3)
    (let $__tr_tuple (collapse (match &self (tick $x) (tick $x)))
      (size-atom $__tr_tuple)))
  7)
