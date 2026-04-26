; Translated from PeTTa to HE (10 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/recursive_types2.metta

(: Z Nat)
(: S (-> Nat Nat))
(: Greater (-> Nat Nat Bool))
(= (Greater (S $x) Z) True)
(= (Greater Z $x) False)
(= (Greater (S $x) (S $y)) (Greater $x $y))
!(assertPeTTaTest (Greater (S Z) (S Z)) false)
!(assertPeTTaTest (Greater (S (S Z)) (S Z)) true)
