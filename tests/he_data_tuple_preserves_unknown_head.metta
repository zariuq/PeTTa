; A returned tuple whose first element is itself a non-callable expression is
; data. The evaluator may reduce explicit eval/call sites, but should not
; eagerly reduce inside an unknown tuple head.

(= (install-data-tuple-fib)
   (let $tmp (add-atom &self
               (= (tuple-fib $N)
                  (if (< $N 2)
                      $N
                      (+ (tuple-fib (- $N 1))
                         (tuple-fib (- $N 2))))))
        ((within (tuple-fib 5))
         (call-within (call (tuple-fib 5)))
         (eval-within (eval (tuple-fib 5))))))

!(assertEqualToResult
  (install-data-tuple-fib)
  (((within (tuple-fib 5))
    (call-within 5)
    (eval-within 5))))
