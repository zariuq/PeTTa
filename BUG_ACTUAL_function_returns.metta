;; ACTUAL BUG: User-defined functions don't return values in PeTTa
;; This is the real blocker, not let or println

!(println! "=== Minimal Bug: Function Return Values ===")

;; Define a simple function that wraps a builtin
(= (my-add $a $b) (+ $a $b))

!(println! "")
!(println! "Test 1: Inline builtin works")
!(+ 2 3)
; Expected: 5
; Actual: 5 ✓

!(println! "")
!(println! "Test 2: User-defined function doesn't return")
!(my-add 2 3)
; Expected: 5
; Actual: () ✗

!(println! "")
!(println! "Test 3: Let with inline builtin works")
!(let $x (+ 2 3)
  (println! $x))
; Expected: prints 5
; Actual: prints 5 ✓

!(println! "")
!(println! "Test 4: Let with user function doesn't work")
!(let $x (my-add 2 3)
  (println! $x))
; Expected: prints 5
; Actual: prints () ✗

!(println! "")
!(println! "=== Same issue with matchc ===")

(= (my-matchc $space $pattern $query)
   (collapse (match $space $pattern $query)))

!(bind! &s (new-space))
!(add-atom &s (Foo bar))

!(println! "")
!(println! "Test 5: Inline collapse/match works")
!(collapse (match &s (Foo $x) $x))
; Expected: ((bar))
; Actual: ((bar)) ✓

!(println! "")
!(println! "Test 6: User-defined matchc doesn't return")
!(my-matchc &s (Foo $x) $x)
; Expected: ((bar))
; Actual: () ✗

!(println! "")
!(println! "=== Conclusion ===")
!(println! "PeTTa bug: User-defined functions return () instead of evaluating their bodies")
!(println! "This breaks ALL custom mmverify functions: matchc, add_c, add_v, verify, etc.")
