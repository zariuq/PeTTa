; Translated from PeTTa to HE (20 atoms)
; Source: examples/lambda.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(: apply (-> Expression %Undefined% %Undefined%))
(= (apply (lambda $var $body) $arg) (unquote (quote (let $var $arg $body))))
(= (applyL1) (apply (lambda $x (+ $x 1)) 2))
(= (applyL2) (apply (lambda ($x $y) (+ $x $y)) (2 7)))
!(assertEqualToEval (applyL1) 3)
!(assertEqualToEval (applyL2) 9)
!(assertEqualToEval (maplist (|-> ($a) (+ 1 $a)) (1 2 3)) (2 3 4))
!(assertEqualToEval ((|-> ($acc $e) (or (== 1 $e) $acc)) False 1) True)
(= (myfunc $a $b) (cons $a $b))
!(assertEqualToEval (let $f (myfunc 42) ((|-> ($x) ($f ($x 2 3))) 43)) (42 43 2 3))
!(assertEqualToEval (((|-> ($x $y) (42 $x $y)) 43) 44) (42 43 44))
(= (myfunc2 $mylambda) ($mylambda 43 44))
!(assertEqualToEval (let* (($k 45) ($lambda (|-> ($x $y) (42 $x $y $k)))) (myfunc2 $lambda)) (42 43 44 45))
