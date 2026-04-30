; Translated from PeTTa to HE (10 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/specializefunctiontypes.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (g $x) $x)
(: f (-> Atom Number Atom))
(: f (-> Atom String Atom))
(= (f $g $x) (repra ($g $x)))
!(f g 42)
!(assertPeTTaTest (match &self (: f_Spec_[g] (-> Atom Number Atom)) ok) ok)
!(assertPeTTaTest (match &self (: f_Spec_[g] (-> Atom String Atom)) ok) ok)
