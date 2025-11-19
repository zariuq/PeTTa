; Test file for Substitution Operations (PeTTa version)
; Testing substitution creation, application, and validation

!(import! &self ../lib/lib_he)
; Note: NOT importing helpers_petta to avoid test pollution

; ===== Function Definitions (Inline for Testing) =====

; adjust-state-additive: Add to state (needed by substitution functions)
(= (adjust-state-additive $state $delta)
  (let $current (get-state $state)
    (change-state! $state (+ $current $delta))))

; flatten-list: Flatten nested lists
(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

; to-list': Convert expression to list with tail
(= (to-list' $expr $tail)
  (if (== $expr ()) $tail
    (Cons (car-atom $expr)
        (to-list' (cdr-atom $expr) $tail))))

; to-list: Convert expression to Cons/Nil
(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

; from-list: Convert Cons/Nil to expression
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

; flatten-expr: Flatten expression
(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

; add-subst: Add substitution to tagged substitution space
; PeTTa adaptation: uses tagged atoms instead of separate space
(= (add-subst $subst-tag $stack $sp ($typecode $var))
  (let* (($sp_val (get-state $sp))
         ($entry (collapse (match &self ($stack ((Num $sp_val) $s)) $s))))
    (case $entry
      ((($e)
         (let* (($entry0 (car-atom $e))
                ($entry_tail (cdr-atom $e))
                ($entry1: (car-atom $entry_tail)))
           (if (== $entry0 $typecode)
               (progn
                 (add-atom &self ($subst-tag ($var $entry1:)))
                 (adjust-state-additive $sp 1)
                 (cons-atom $var (cons-atom $entry1: ())))
               (Error ((sp $sp_val) (entry $e) (typecode $typecode) (var $var))
                      "Proof stack entry does not match floating hypothesis."))))
       (() (Error ((sp $sp_val) (typecode $typecode) (var $var))
                  "Stack entry not found"))))))

; apply_subst_tok: Apply substitution to a single token
; PeTTa adaptation: use tagged atom lookup
(= (apply_subst_tok $subst-tag $tok)
  (let $result (collapse (match &self ($subst-tag ($tok $sub)) $sub))
    (case $result
      ((($sub) $sub)
       (() $tok)))))

; apply_subst_to_expr: Recursively apply substitution preserving structure
(= (apply_subst_to_expr $subst-tag ())  ())
(= (apply_subst_to_expr $subst-tag $expr)
  (if (== (get-metatype $expr) Symbol)
      (apply_subst_tok $subst-tag $expr)
      (let ($head $tail) (decons-atom $expr)
        (cons-atom (apply_subst_to_expr $subst-tag $head)
                   (apply_subst_to_expr $subst-tag $tail)))))

; apply_subst: Apply substitution to entire statement
(= (apply_subst $subst-tag $stmt)
  (apply_subst_to_expr $subst-tag $stmt))

; check_subst: Check that substituted essential hypothesis matches stack
(= (check_subst $subst-tag $stack $sp $ehyp)
  (let* (($sp_val (get-state $sp))
         ($entry (collapse (match &self ($stack ((Num $sp_val) $s)) $s)))
         ($subst_h (apply_subst $subst-tag $ehyp)))
    (case $entry
      ((($e)
         (if (== $e $subst_h)
             (progn (adjust-state-additive $sp 1) ())
             (Error ((sp $sp_val) (entry $e) (ehyp $ehyp) (subst_h $subst_h))
                    "Proof stack entry does not match essential hypothesis.")))
       (() (Error ((sp $sp_val) (ehyp $ehyp))
                  "Stack entry not found"))))))

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
