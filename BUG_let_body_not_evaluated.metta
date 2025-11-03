;; MINIMAL BUG REPRODUCTION: let body not evaluated in PeTTa
;; This demonstrates that let expressions with certain function calls
;; return () instead of evaluating their bodies

!(println! "=== Bug Demonstration ===")

!(println! "")
!(println! "Test 1: Simple let with literal value works")
!(let $x 42
  (println! "✓ This prints - simple let works"))

!(println! "")
!(println! "Test 2: Let with function result doesn't evaluate body")
!(bind! &space (new-space))
!(add-atom &space (Foo bar))

;; This let should evaluate the body and print "Got result"
;; But in PeTTa, if matchc returns (), the body never executes
!(let $result (matchc &space (Foo $x) $x)
  (let () (println! $result)
    (println! "✓ BUG CHECK: Did this print?")))

!(println! "")
!(println! "Test 3: Check if result was actually returned")
!(let $result (matchc &space (Foo $x) $x)
  (if (== $result (bar))
    (println! "✓ Got expected result 'bar'")
    (if (== $result ())
      (println! "✗ BUG: matchc returned () instead of matching")
      (let () (println! $result)
        (println! "Got unexpected result")))))

!(println! "")
!(println! "Test 4: Direct println works")
!(println! "✓ Direct println always works")

!(println! "")
!(println! "=== End Bug Demonstration ===")
!(println! "Expected: All messages should print")
!(println! "Actual in PeTTa: Only Tests 1 and 4 print, Tests 2 and 3 return ()")
