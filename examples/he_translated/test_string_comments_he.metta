; Translated from PeTTa to HE (23 atoms)
; Source: examples/test_string_comments.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
!(assertEqualToEval ")" ")")
!(assertEqualToEval "(" "(")
!(assertEqualToEval ";" ";")
!(assertEqualToEval (quoted-syntax (quote ";")) ";")
!(assertEqualToEval "foo;bar" "foo;bar")
!(assertEqualToEval ";;;" ";;;")
!(assertEqualToEval ";start" ";start")
!(assertEqualToEval "end;" "end;")
!(assertEqualToEval "quote: \"" "quote: \"")
!(assertEqualToEval "path\\file" "path\\file")
(= (test-func) result)
!(assertEqualToEval (test-func) result)
