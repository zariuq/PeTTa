; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/case2.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (compile $stmt) (case $stmt (($stmt (superpose (what what2))))))
!(assertPeTTaTest (collapse (compile wat)) (what what2))
