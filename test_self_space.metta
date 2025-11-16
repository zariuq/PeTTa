!(import! &self lib/lib_he)

!(println! "=== Testing match with &self ===")
!(println! "")

!(add-atom &self (test-atom value))
!(println! "Added (test-atom value) to &self")

!(println! "Test 1: Match in &self")
!(test (collapse (match &self (test-atom value) FOUND)) (FOUND))
