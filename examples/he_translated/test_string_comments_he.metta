; Translated from PeTTa to HE (23 atoms)
; Source: examples/test_string_comments.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

(= (quoted-syntax (quote $expr)) $expr)
!(test ")" ")")
!(test "(" "(")
!(test ";" ";")
!(test (quoted-syntax (quote ";")) ";")
!(test "foo;bar" "foo;bar")
!(test ";;;" ";;;")
!(test ";start" ";start")
!(test "end;" "end;")
!(test "quote: \"" "quote: \"")
!(test "path\\file" "path\\file")
(= (test-func) result)
!(test (test-func) result)
