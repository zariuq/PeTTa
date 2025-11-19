; Test file for Substitution Operations (PeTTa version)
; Testing substitution creation, application, and validation

!(import! &self ../lib/lib_he)
!(import! &self mmverify-utils_petta)

; ===== Tests =====

!(println! "=== Testing Substitution Operations ===")
!(println! "")

!(println! "Test 1: apply_subst_tok - token not in substitution")
!(test (apply_subst_tok subst1 x) x)

!(println! "Test 2: apply_subst_tok - token found in substitution")
!(add-atom &self (subst2 (ph (wff P))))
!(test (apply_subst_tok subst2 ph) (wff P))
!(test (apply_subst_tok subst2 ps) ps)

!(println! "Test 3: apply_subst - simple statement with no variables")
!(test (apply_subst subst3 (wff P -> Q)) (wff P -> Q))

!(println! "Test 4: apply_subst - substitute one variable")
!(add-atom &self (subst4 (ph (wff A))))
!(test (apply_subst subst4 (-> ph (wff B)))
       (-> (wff A) (wff B)))

!(println! "Test 5: apply_subst - substitute multiple variables")
!(add-atom &self (subst5 (ph (wff X))))
!(add-atom &self (subst5 (ps (wff Y))))
!(test (apply_subst subst5 (-> ph ps))
       (-> (wff X) (wff Y)))

!(println! "Test 6: apply_subst - variable appears multiple times")
!(add-atom &self (subst6 (ph (wff A))))
!(test (apply_subst subst6 (-> ph (-> ph ph)))
       (-> (wff A) (-> (wff A) (wff A))))

!(println! "Test 7: add-subst - successful match")
!(add-atom &self (stack7 ((Num 0) (wff (-> P Q)))))
!(bind! &sp7 (new-state 0))
!(test (add-subst subst7 stack7 &sp7 (wff ph))
       (ph (-> P Q)))
!(test (get-state &sp7) 1)

!(println! "Test 8: add-subst - verify substitution was added")
!(test (apply_subst_tok subst7 ph) (-> P Q))

!(println! "Test 9: add-subst - typecode mismatch")
!(add-atom &self (stack9 ((Num 0) (class X))))
!(bind! &sp9 (new-state 0))
!(test (case (add-subst subst9 stack9 &sp9 (wff ph))
         (((Error $data $msg) (Error))
          ($_ not-error)))
       (Error))

!(println! "Test 10: check_subst - match succeeds")
!(add-atom &self (stack10 ((Num 0) (wff (-> A B)))))
!(add-atom &self (subst10 (ph A)))
!(add-atom &self (subst10 (ps B)))
!(bind! &sp10 (new-state 0))
!(test (check_subst subst10 stack10 &sp10 (wff (-> ph ps)))
       ())
!(test (get-state &sp10) 1)

!(println! "Test 11: check_subst - match fails")
!(add-atom &self (stack11 ((Num 0) (wff (-> X Y)))))
!(add-atom &self (subst11 (ph A)))
!(add-atom &self (subst11 (ps B)))
!(bind! &sp11 (new-state 0))
!(test (case (check_subst subst11 stack11 &sp11 (wff (-> ph ps)))
         (((Error $data $msg) (Error))
          ($_ not-error)))
       (Error))

!(println! "Test 12: Complex substitution with nested expressions")
!(add-atom &self (subst12 (ph (wff (-> P Q)))))
!(add-atom &self (subst12 (ps (wff (-> Q R)))))
!(test (apply_subst subst12 (-> (-> ph ps) ph))
       (-> (-> (wff (-> P Q)) (wff (-> Q R))) (wff (-> P Q))))

!(println! "Test 13: Substitution with mixed variables and constants")
!(add-atom &self (subst13 (x (class A))))
!(test (apply_subst subst13 (union x (class B)))
       (union (class A) (class B)))

!(println! "Test 14: add-subst updates stack pointer correctly")
!(add-atom &self (stack14 ((Num 0) (wff P))))
!(add-atom &self (stack14 ((Num 1) (wff Q))))
!(bind! &sp14 (new-state 0))
!(add-subst subst14 stack14 &sp14 (wff ph))
!(test (get-state &sp14) 1)
!(add-subst subst14 stack14 &sp14 (wff ps))
!(test (get-state &sp14) 2)

!(println! "")
!(println! "=== All substitution tests complete ===")
