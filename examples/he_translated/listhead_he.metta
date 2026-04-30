; Translated from PeTTa to HE (8 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/listhead.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (len ()) 0)
(= (len (cons $Head $Tail)) (let $N0 (len $Tail) (+ $N0 1)))
!(assertPeTTaTest (let (cons $Head $Tail) (1 2 3 4 5 6) ($Head $Tail)) (1 (2 3 4 5 6)))
!(assertPeTTaTest (len (1 2 3)) 3)
!(assertPeTTaTest (cons 42 ()) (42))
