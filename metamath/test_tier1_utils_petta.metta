; Test file for Tier 1 utility functions (PeTTa version)
; Testing missing utilities: match-atom, update-atom, state operations, etc.

!(import! &self ../lib/lib_he)
!(import! &self mmverify-utils_petta)

; ===== Tests =====

!(println! "=== Testing Tier 1 Utility Functions ===")
!(println! "")

!(println! "Test 1: match-atom - find atom in expression")
!(test   (match-atom (a b c) b yes)
  yes)

!(println! "Test 2: match-atom - multiple occurrences")
!(test   (collapse (match-atom (x y x) x found))
  (found found))

!(println! "Test 3: match-atom' - with empty handling")
!(test   (match-atom' (a b c) z no-match)
  ())

!(println! "Test 4: match-atom'' - with custom empty")
!(test   (match-atom'' (a b c) z found not-found)
  not-found)

!(println! "Test 5: update-atom - update tagged atom")
!(add-atom &self (TestSpace (Data 42)))
!(update-atom (TestSpace (Data 42)) (TestSpace (Data 100)))
!(test   (collapse (match &self (TestSpace (Data $x)) $x))
  (100))

!(println! "Test 6: adjust-state-additive - increment state")
!(bind! &counter (new-state 0))
!(adjust-state-additive &counter 5)
!(test   (get-state &counter)
  5)

!(println! "Test 7: adjust-state-subtractive - decrement state")
!(adjust-state-subtractive &counter 3)
!(test   (get-state &counter)
  2)

!(println! "Test 8: remove_from_stack - clear stack entries")
!(add-atom &self ((Num 0) (entry 0)))
!(add-atom &self ((Num 1) (entry 1)))
!(add-atom &self ((Num 2) (entry 2)))
!(remove_from_stack 1 3)
!(test   (collapse (match &self ((Num 1) $e) $e))
  ())

!(println! "Test 9: empty-space - clear all tagged atoms")
!(add-atom &self (TestSpace2 val1))
!(add-atom &self (TestSpace2 val2))
!(empty-space TestSpace2)
!(test   (collapse (match &self (TestSpace2 $v) $v))
  ())

!(println! "")
!(println! "=== All Tier 1 utility tests complete ===")
