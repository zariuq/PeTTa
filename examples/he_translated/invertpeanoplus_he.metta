; Translated from PeTTa to HE (12 atoms)
; Source: examples/invertpeanoplus.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (plus Z $y) $y)
(= (plus (S $x) $y) (S (plus $x $y)))
!(test (plus (S (S Z)) (S Z)) (S (S (S Z))))
!(test (let (plus $A (S Z)) (S (S (S (S Z)))) $A) (S (S (S Z))))
!(test (let (plus (S Z) $B) (S (S (S (S Z)))) $B) (S (S (S Z))))
!(test (collapse (let (plus $A $B) (S (S (S (S Z)))) ($A $B))) ((Z (S (S (S (S Z))))) ((S Z) (S (S (S Z)))) ((S (S Z)) (S (S Z))) ((S (S (S Z))) (S Z)) ((S (S (S (S Z)))) Z)))
!(test (once (let (plus $A $B) (S (S (S (S Z)))) ($A $B))) (Z (S (S (S (S Z))))))
