; Legacy metamath-test fixture paths should resolve to the restored textual
; parser fixtures, and the comment-only file should still reject cleanly.

!(import! &self cverify_compat)

!(assertEqual
  (fs-exists? (resolve-input-path "../../hyperon/metamath/metamath-test/tests/core/small/comment1.mm"))
  True)

!(assertEqualToResult
  (parse_mm_file "../../hyperon/metamath/metamath-test/tests/core/small/comment1.mm")
  (parse-unsupported))
