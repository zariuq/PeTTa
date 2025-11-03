!(println! "=== MVP: case doesn't evaluate in PeTTa ===")
!(println! "")

;; Simple case test
(= (test-case $val)
   (case $val
     ((empty result-empty)
      (full result-full))))

!(println! "Test 1: Simple case")
!(test-case empty)
!(test-case full)

!(println! "")

;; What unify actually does
!(bind! &kb (new-space))
!(add-atom &kb (Foo bar))

(= (unify-test $space $pattern)
   (let $results (collapse (match $space $pattern $pattern))
     (case $results
       (() not-found)
       (Empty not-found)
       ($_ found))))

!(println! "Test 2: unify pattern (match + case)")
!(unify-test &kb (Foo bar))
!(unify-test &kb (Missing item))

!(println! "")

;; Compare with if
(= (unify-with-if $space $pattern)
   (let $results (collapse (match $space $pattern $pattern))
     (if (== $results ())
         not-found
         found)))

!(println! "Test 3: Using if instead of case")
!(test (unify-with-if &kb (Foo bar)) found)
!(test (unify-with-if &kb (Missing item)) not-found)

!(println! "")
!(println! "Expected: Test 1 and 2 should evaluate, Test 3 passes ✅")
!(println! "Actual in PeTTa: Test 1 and 2 return unevaluated case expressions")
