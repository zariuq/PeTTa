; Translated from PeTTa to HE (23 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/test_string_comments.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertPeTTaTest ")" ")")
!(assertPeTTaTest "(" "(")
!(assertPeTTaTest ";" ";")
!(assertPeTTaTest (quote ";") ";")
!(assertPeTTaTest "foo;bar" "foo;bar")
!(assertPeTTaTest ";;;" ";;;")
!(assertPeTTaTest ";start" ";start")
!(assertPeTTaTest "end;" "end;")
!(assertPeTTaTest "quote: \"" "quote: \"")
!(assertPeTTaTest "path\\file" "path\\file")
(= (test-func) result)
!(assertPeTTaTest (test-func) result)
