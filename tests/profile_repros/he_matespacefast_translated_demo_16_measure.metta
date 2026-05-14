; Large translated-shape HE witness for the matespacefast path.
; This aims to preserve the full translated growth/collapse shape while still
; finishing well below the full K=19 example.

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

!(let $__tr_tuple_1 (collapse (mate-space-demo 16))
   (size-atom $__tr_tuple_1))
