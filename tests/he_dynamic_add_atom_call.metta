; Under --he, runtime-added user equations live behind the internal
; MeTTa-user namespace. Explicit `call` must target that namespace too.

(= (install-dyn-fib)
   (let $tmp (add-atom &self
               (= (dyn-fib $N)
                  (if (< $N 2)
                      $N
                      (+ (dyn-fib (- $N 1))
                         (dyn-fib (- $N 2))))))
        (call (dyn-fib 5))))

!(assertEqual (install-dyn-fib) 5)
