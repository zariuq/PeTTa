; Translated from PeTTa to HE (12 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/invertpeanoplus.metta

(= (plus Z $y) $y)
(= (plus (S $x) $y) (S (plus $x $y)))
!(assertPeTTaTest (plus (S (S Z)) (S Z)) (S (S (S Z))))
!(assertPeTTaTest (let (plus $A (S Z)) (S (S (S (S Z)))) $A) (S (S (S Z))))
!(assertPeTTaTest (let (plus (S Z) $B) (S (S (S (S Z)))) $B) (S (S (S Z))))
!(assertPeTTaTest (collapse (let (plus $A $B) (S (S (S (S Z)))) ($A $B))) ((Z (S (S (S (S Z))))) ((S Z) (S (S (S Z)))) ((S (S Z)) (S (S Z))) ((S (S (S Z))) (S Z)) ((S (S (S (S Z)))) Z)))
!(assertPeTTaTest (once (let (plus $A $B) (S (S (S (S Z)))) ($A $B))) (Z (S (S (S (S Z))))))
