; Translated from PeTTa to HE (8 atoms)
; Source: examples/listhead.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (len ()) 0)
(= (len (cons $Head $Tail)) (let $N0 (len $Tail) (+ $N0 1)))
!(assertEqualToEval (let (cons $Head $Tail) (1 2 3 4 5 6) ($Head $Tail)) (1 (2 3 4 5 6)))
!(assertEqualToEval (len (1 2 3)) 3)
!(assertEqualToEval (cons 42 ()) (42))
