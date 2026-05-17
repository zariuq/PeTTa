; Translated from PeTTa to HE (14 atoms)
; Source: examples/test_unify_eval_branches.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering


!(import! &self lib/lib_he)
(Constant wff (Type "$c"))
(Var x 0 (Type "$v"))
!(assertEqualToEval (unify &self (Constant wff (Type "$c")) (Error (Constant wff) "already declared") ()) (Error (Constant wff) "already declared"))
!(assertEqualToEval (unify &self (Constant y (Type "$c")) (Error (Constant y) "already declared") (unify &self (Var y 0 (Type "$v")) (Error (Var y) "active variable conflict") ())) ())
!(assertEqualToEval (unify &self (Constant x (Type "$c")) (Error (Constant x) "already declared") (unify &self (Var x 0 (Type "$v")) (Error (Var x) "active variable conflict") ())) (Error (Var x) "active variable conflict"))
!(assertEqualToEval (unify &self (Constant wff (Type "$c")) (+ 1 2) 0) 3)
!(assertEqualToEval (unify &self (Constant NOSUCH (Type "$c")) 0 (+ 10 20)) 30)
