; Translated from PeTTa to HE (3 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/logicprogset.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (myf $M) (and (and (member a $M) (member b $M)) (== (size-atom $M) 2)))
!(assertPeTTaTest (if (once (myf $M)) $M) (a b))
