; Translated from PeTTa to HE (14 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/matchtypes.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (match-types $A $B $Then $Else) (if (== $A $B) $Then $Else))
!(match-types Atom Atom "Matched!" "Didn't match")
!(match-types Atom Number "Matched!" "Didn't match")
(= (match-type-or $value $type1 $type2) (match-types $type1 $type2 True $value))
!(assertPeTTaTest (match-type-or True Number Number) True)
!(assertPeTTaTest (match-type-or False Number Number) True)
!(assertPeTTaTest (match-type-or True Number Bool) True)
!(assertPeTTaTest (match-type-or False Number Bool) False)
