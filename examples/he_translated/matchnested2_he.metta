; Translated from PeTTa to HE (7 atoms)
; Source: examples/matchnested2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (hide $1) (empty))
!(hide ((add-atom &self (friend tim tom)) (add-atom &self (friend tom tam)) (add-atom &self (friend sim som)) (add-atom &self (friend som sam))))
!(hide (match &self (, (friend $1 $2) (friend $2 $3)) ((add-atom &self (transitive $1 $2 $3)) (remove-atom &self (friend $1 $2)) (remove-atom &self (friend $2 $3)))))
!(assertEqualToEval (msort (collapse (match &self (transitive $1 $2 $3) (transitive $1 $2 $3)))) ((transitive sim som sam) (transitive tim tom tam)))
