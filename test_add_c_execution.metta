!(println! "Testing add_c execution order")
!(bind! &kb (new-space))

;; Simpler version to debug
(= (check-const $space $tok)
   (match $space (Constant $tok (Type "$c")) found))

(= (add_c_simple $space $tok)
   (case (check-const $space $tok)
     ((Empty (add-atom $space (Constant $tok (Type "$c"))))
      (found (Error already-exists)))))

!(println! "")
!(println! "Test 1: Check non-existent constant:")
!(check-const &kb foo)

!(println! "")
!(println! "Test 2: Add foo using add_c_simple:")
!(add_c_simple &kb foo)

!(println! "")
!(println! "Test 3: Check if foo exists now:")
!(check-const &kb foo)

!(println! "")
!(println! "Test 4: Try to add foo again:")
!(add_c_simple &kb foo)

!(println! "")
!(println! "What's actually in &self:")
!(match &self (subspace kb $x) $x)