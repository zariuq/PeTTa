; Quoted code routed through a variable into eval must execute as code input.

!(test (eval (fib 5))
       (quote (fib 5)))

!(add-atom &self (= (g $x $y) (+ $x $y)))
!(test (let $e (quote (g 3 4)) (eval $e))
       7)
!(remove-atom &self (= (g $x $y) (+ $x $y)))
!(test (let $e (quote (g 3 4)) (eval $e))
       (g 3 4))
