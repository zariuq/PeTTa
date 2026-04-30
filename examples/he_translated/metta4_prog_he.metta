; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/metta4_prog.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest (chain (add-atom &self (friend sam tom)) $__tr_discard_1 (chain (remove-atom &self (friend sam tom)) $__tr_discard_2 (chain (add-atom &self (friend sam tim)) $__tr_discard_3 (match &self (friend sam $1) $1)))) tim)
!(assertPeTTaTest (let $__tr_result_4 1 (chain 2 $__tr_discard_5 (chain 3 $__tr_discard_6 $__tr_result_4))) 1)
!(assertPeTTaTest (chain 1 $__tr_discard_7 (chain 2 $__tr_discard_8 3)) 3)
