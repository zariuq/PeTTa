; Reduced HE witness for profiling the translated matespacefast path.
; This keeps the direct recursive rewrite shape, but returns the count instead
; of halting via test so the profiling harness can emit counters on mismatch.

(= (count-demo $expr)
   (let $tuple (eval $expr)
        (size-atom $tuple)))

(= (rewriteK $t $n)
   (if (== $n 0)
       done
       (let* (($_1 (add-atom &self (num (M $t))))
              ($_2 (add-atom &self (num (W $t))))
              ($_3 (add-atom &self (num (C $t)))))
             ((rewriteK (M $t) (- $n 1))
              (rewriteK (W $t) (- $n 1))))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (rewriteK Z $K)))
         (match &self (num $1) (num $1))))

!(count-demo (collapse (mate-space-demo 6)))
