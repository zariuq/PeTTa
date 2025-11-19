!(import! &self ../lib/lib_he)

; PeTTa Test: println! in let* expressions
; This demonstrates that println! FAILS in let* in PeTTa

!(println! "=== PeTTa: Testing println! in let* ===")
!(println! "")

!(println! "Test 1: println! with ! in let* with (() ...) pattern")
!(let*
  (
    ($a 1)
    ($_1 (println! ("❌ PeTTa: Inside let*, a =" $a)))
    ($b 2)
  )
  (+ $a $b))
!(println! "Test 1 complete")
!(println! "")

!(println! "Test 2: Multiple println! statements in let*")
!(let*
  (
    ($x 10)
    ($_1 (println! ("❌ PeTTa: x =" $x)))
    ($y 20)
    ($_2 (println! ("❌ PeTTa: y =" $y)))
    ($z (+ $x $y))
    ($_3 (println! ("❌ PeTTa: z = x + y =" $z)))
  )
  $z)
!(println! "Test 2 complete")
!(println! "")

!(println! "Test 3: println! in progn (DOES work in PeTTa)")
!(progn
  (println! "✅ PeTTa: Inside progn 1")
  (println! "✅ PeTTa: Inside progn 2")
  (+ 1 2))
!(println! "Test 3 complete")
!(println! "")

!(println! "Test 4: Using prog1 for side effects (DOES work in PeTTa)")
!(prog1
  42
  (println! "✅ PeTTa: Inside prog1, returning 42"))
!(println! "Test 4 complete")
!(println! "")

!(println! "=== PeTTa tests complete ===")