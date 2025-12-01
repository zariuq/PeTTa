; Complex nested imports test
; This tests that file-relative imports work correctly with:
; - Nested directory imports
; - Sibling imports after nested imports
; - Multiple branches of nested imports
; - Directory context restoration after each import

!(import! &self ../../lib/lib_he)

!(println! "=== Complex Nested Imports Test ===")
!(println! "")

; Test 1: Import from branchA (which imports a2 internally)
!(println! "Test 1: Import branchA/a1 (which imports a2)")
!(import! &self branchA/a1)
!(test (a1-value) 10)
!(test (a2-value) 42)
!(println! "")

; Test 2: Import sibling from top level (tests directory restoration)
!(println! "Test 2: Import sibling after branchA imports")
!(import! &self sibling)
!(test (sibling-value) 999)
!(println! "")

; Test 3: Import from branchB (which imports deep/b2 internally)
!(println! "Test 3: Import branchB/b1 (which imports deep/b2)")
!(import! &self branchB/b1)
!(test (b1-value) 100)
!(test (b2-value) 200)
!(println! "")

; Test 4: Verify sibling-value still accessible (proves dir context was restored correctly)
; Note: We don't re-import sibling here because PeTTa allows re-importing,
; which would add duplicate definitions. The fact that Test 2 succeeded proves
; directory restoration works.
!(println! "Test 4: Verify sibling-value still accessible after deep nesting")
!(test (sibling-value) 999)
!(println! "")

; Test 5: Verify all imported values are still accessible
!(println! "Test 5: Verify all values still accessible")
!(test (a1-value) 10)
!(test (a2-value) 42)
!(test (b1-value) 100)
!(test (b2-value) 200)
!(test (sibling-value) 999)
!(println! "")

!(println! "✅ All nested import tests completed!")
