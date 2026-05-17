; Translated from PeTTa to HE (23 atoms)
; Source: examples/pln_direct.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
!(import! &self (library lib_pln))
(: => (-> Expression Expression Atom Atom))
(= (=> (cons , $args) $C $stvImp) (chain (cut) $__tr_discard_1 (add-atom &self (= $C (Truth_ModusPonens (foldl-atom $args (stv 1.0 1.0) $__tr_acc_2 $__tr_item_3 (eval (Truth_ModusPonens $__tr_acc_2 $__tr_item_3))) $stvImp)))))
(= (=> $A $C $stvImp) (add-atom &self (= $C (Truth_ModusPonens $A $stvImp))))
(: ? (-> Expression Atom))
(= (? $term) (collapse (unique ($term (chain (unquote (quote $term)) $__tr_discard_4 (foldl-atom (collapse (unquote (quote $term))) (stv 0.5 0.0) $__tr_acc_5 $__tr_item_6 (eval (Truth_Revision $__tr_acc_5 $__tr_item_6))))))))
!(=> (, (father $a $b) (father $b $c)) (grandfather $a $c) (stv 1.0 0.9))
!(=> (, (father $a $b) (mother $b $c)) (grandfather $a $c) (stv 1.0 0.9))
!(=> (grandfather $a $x) (old $a) (stv 1.0 0.9))
(= (father a b) (stv 1.0 0.9))
(= (father b c) (stv 1.0 0.9))
(= (father a y) (stv 1.0 0.9))
(= (mother y c) (stv 0.0 0.9))
!(assertEqualToEval (? (grandfather a c)) (quoted-syntax (quote (((grandfather a c) (stv 0.51 0.8432620011567381))))))
!(assertEqualToEval (? (grandfather $who c)) (quoted-syntax (quote (((grandfather a c) (stv 0.51 0.8432620011567381))))))
!(assertEqualToEval (? (old $who)) (quoted-syntax (quote (((old a) (stv 0.5198 0.7923434575206812))))))
