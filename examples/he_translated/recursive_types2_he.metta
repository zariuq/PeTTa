; Translated from PeTTa to HE (10 atoms)
; Source: examples/recursive_types2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(: Z Nat)
(: S (-> Nat Nat))
(: Greater (-> Nat Nat Bool))
(= (Greater (S $x) Z) True)
(= (Greater Z $x) False)
(= (Greater (S $x) (S $y)) (Greater $x $y))
!(test (Greater (S Z) (S Z)) false)
!(test (Greater (S (S Z)) (S Z)) true)
