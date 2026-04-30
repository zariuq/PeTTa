; Reduced HE witness for the translated matespacefast path.
; This keeps the direct recursive rewrite shape but bounds the depth so the
; full example's timeout can be separated from semantic correctness.

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

!(test
  (count-demo (collapse (mate-space-demo 6)))
  190)
