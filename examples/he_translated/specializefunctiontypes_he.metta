; Translated from PeTTa to HE (10 atoms)
; Source: examples/specializefunctiontypes.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (g $x) $x)
(: f (-> Atom Number Atom))
(: f (-> Atom String Atom))
(= (f $g $x) (repra ($g $x)))
!(f g 42)
!(assertEqualToEval (match &self (: f_Spec_[g] (-> Atom Number Atom)) ok) ok)
!(assertEqualToEval (match &self (: f_Spec_[g] (-> Atom String Atom)) ok) ok)
