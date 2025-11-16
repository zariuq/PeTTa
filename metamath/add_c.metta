!(import! &self ../lib/lib_he)

;; PeTTa version of add_c using &self with tagged atoms
;; CRITICAL: PeTTa's match DOES NOT WORK with new-space!
;; Workaround: Use &self and tag all atoms with a space identifier

(= (add_c $space-tag $tok)
   (case (collapse (match &self ($space-tag (Constant $tok (Type "$c"))) found))
     (((found)
        (Error (Constant $tok) "Constant already declared."))
      (()
        (case (collapse (match &self ($space-tag (Var $tok $_ (Type "$v"))) found))
          (((found)
             (Error (Var $tok) "Trying to declare as a constant an active variable."))
           (()
             (let $_ (add-atom &self ($space-tag (Constant $tok (Type "$c"))))
               (Constant $tok (Type "$c"))))))))))

!(println! "=== Testing add_c ===")
!(println! "")

;; Test 1: Add new constant
!(println! "Test 1: Add new constant 'foo' to kb1")
!(test (add_c kb1 foo) (Constant foo (Type "$c")))
!(println! "")

;; Test 2: Verify constant exists
!(println! "Test 2: Verify 'foo' exists in kb1")
!(test (collapse (match &self (kb1 (Constant foo (Type "$c"))) FOUND)) (FOUND))
!(println! "")

;; Test 3: Try to add duplicate
!(println! "Test 3: Try to add duplicate 'foo' - should return Error")
!(test (add_c kb1 foo) (Error (Constant foo) "Constant already declared."))
!(println! "")

;; Test 4: Variable conflict
!(add-atom &self (kb2 (Var x 1 (Type "$v"))))
!(println! "Test 4: Constant 'x' conflicts with var 'x' in kb2 - should return Error")
!(test (add_c kb2 x) (Error (Var x) "Trying to declare as a constant an active variable."))
!(println! "")

;; Test 5: Multiple constants in same tagged space
!(println! "Test 5: Add multiple constants to kb3")
!(test (add_c kb3 zero) (Constant zero (Type "$c")))
!(test (add_c kb3 plus) (Constant plus (Type "$c")))

!(println! "")
!(println! "=== All tests complete ===")
