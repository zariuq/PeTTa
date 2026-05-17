; Dynamic eval should evaluate materialized data returned by match/let,
; while leaving irreducible atom-headed calls as raw source data.

(= (dyn-eval-pair $L $a $b)
   (let $result (+ $a $b)
        (append ($result) $L)))

!(assertEqual
  (let $body (match &self (= (dyn-eval-pair (42) 40.7 2) $x) $x)
       (eval $body))
  (42.7 42))

!(assertEqual
  (eval (unknown-dynamic-eval-probe 1 2))
  (eval (unknown-dynamic-eval-probe 1 2)))
