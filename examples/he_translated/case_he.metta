; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/case.metta

(= (casetest $x) (case $x ((4 42) ($otherpattern 44) ($otherother $45))))
!(assertPeTTaTest (casetest 5) 44)
