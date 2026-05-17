(= (memo-fib $n)
   (if (< $n 2)
       $n
       (+ (memo-fib (- $n 1))
          (memo-fib (- $n 2)))))

!(assertEqualToEval (memo-fib 20) 6765)

!(add-atom &self (= (memo-swap $x) (+ $x 1)))
!(assertEqualToEval (memo-swap 4) 5)
!(remove-atom &self (= (memo-swap $x) (+ $x 1)))
!(add-atom &self (= (memo-swap $x) (+ $x 2)))
!(assertEqualToEval (memo-swap 4) 6)
