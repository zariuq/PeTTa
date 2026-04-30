; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/case.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (casetest $x) (case $x ((4 42) ($otherpattern 44) ($otherother $45))))
!(assertPeTTaTest (casetest 5) 44)
