; Translated from PeTTa to HE (8 atoms)
; Source: examples/invertfunction.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (f $X $Y) (append ($X) $Y))
(= (g $X $Y $Z) (append ((#+ $X $Z)) $Y))
!(test (let (cons $Head $Tail) (1 2 3 4 5 6) ($Head $Tail)) (1 (2 3 4 5 6)))
!(test (let (f $Head $Tail) (1 2 3 4 5 6) ($Head $Tail)) (1 (2 3 4 5 6)))
!(test (let (g $X $Y 35) (42 2 3) ($X $Y 40)) (7 (2 3) 40))
