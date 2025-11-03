!(println! "=== DIAGNOSIS: match works in top-level, fails in runtime-defined functions ===")
!(println! "")

!(bind! &kb (new-space))
!(add-atom &kb (Color red))

;; This is a TOP-LEVEL function definition (parsed at load time)
(= (works-top-level $space $pattern)
   (let $results (collapse (match $space $pattern $pattern))
     (if (== $results ())
         not-found
         found)))

!(println! "Test 1: Top-level function")
!(test (works-top-level &kb (Color red)) found)

!(println! "")
!(println! "Test 2: Runtime-defined function (using equal)")
!(= (fails-runtime $space $pattern)
   (let $results (collapse (match $space $pattern $pattern))
     (if (== $results ())
         not-found
         found)))

!(println! "Calling runtime-defined function:")
!(fails-runtime &kb (Color red))

!(println! "")
!(println! "DIAGNOSIS:")
!(println! "- Top-level functions: match works ✅")
!(println! "- Runtime-defined functions: match fails with 'Unknown procedure' ❌")
!(println! "")
!(println! "This explains why lib/lib_he.metta's unify works")
!(println! "(it's top-level), but test functions defined with ! fail")
