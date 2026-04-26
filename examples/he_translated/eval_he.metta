; Translated from PeTTa to HE (6 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/eval.metta

(= (f $L $a $b) (let $result (+ $a $b) (append ($result) $L)))
!(assertPeTTaTest (let $fbody_specialized (match &self (= (f (42) 40.7 2) $x) $x) (eval $fbody_specialized)) (42.7 42))
(= (evalCustom $body) (let* (($a (add-atom &self (= (myfunc) $body))) ($res (eval (myfunc))) ($r (remove-atom &self (= (myfunc) $body)))) $res))
!(assertPeTTaTest (evalCustom (match &self (= (f (42) 40.7 2) $x) $x)) (42.7 42))
