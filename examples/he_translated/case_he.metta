; Translated from PeTTa to HE (3 atoms)
; Source: examples/case.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (casetest $x) (case $x ((4 42) ($otherpattern 44) ($otherother $45))))
!(assertEqualToEval (casetest 5) 44)
