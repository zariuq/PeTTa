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

(= (mate-space-ones $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (rewriteK Z $K)))
         (match &self (num $1) ok)))

(= (rewriteTagK $t $n)
   (if (== $n 0)
       done
       (let* (($_1 (add-atom &self (tag (M $t))))
              ($_2 (add-atom &self (tag (W $t))))
              ($_3 (add-atom &self (tag (C $t)))))
             ((rewriteTagK (M $t) (- $n 1))
              (rewriteTagK (W $t) (- $n 1))))))

(= (tag-space-ones $K)
   (let* (($s (add-atom &self (tag Z)))
          ($g (rewriteTagK Z $K)))
         (match &self (tag $1) ok)))

!(assertEqualToEval (let $tuple (collapse (mate-space-demo 3)) (size-atom $tuple)) 22)
!(assertEqualToEval (let $tuple (collapse (tag-space-ones 3)) (size-atom $tuple)) 22)
