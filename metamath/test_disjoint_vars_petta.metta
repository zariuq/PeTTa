; Test file for Disjoint Variable functions (PeTTa version)
; Testing DV checking, variable lookups, and constraint validation

!(import! &self ../lib/lib_he)
; Note: NOT importing helpers_petta to avoid test pollution

; ===== Function Definitions (Inline for Testing) =====

; map-pairs: Map function over all pairs from two lists
(= (map-pairs $list1 $list2 $fn)
   (map-atom $list1 $v1
     (map-atom $list2 $v2
       ($fn $v1 $v2))))

; is_var: Check if token is a variable
; PeTTa adaptation: use tagged match with collapse+case
(= (is_var $kb-tag $tok)
  (case (collapse (match &self ($kb-tag (Var $tok $_ (Type "$v"))) found))
    (((found) True)
     (() False))))

; find_vars: Find all tokens in statement that are variables
; PeTTa adaptation: use filter-atom with is_var
(= (find_vars $kb-tag $stmt)
  (filter-atom $stmt $tok (is_var $kb-tag $tok)))

; string<: String comparison for ordering
; PeTTa version: use @< instead of py-dot
(= (string< $x $y)
  (let ($str_x $str_y) ((repr $x) (repr $y))
    (@< $str_x $str_y)))

; orient_pair: Order two variables alphabetically for canonical DV storage
(= (orient_pair $x $y)
   (let ($str_x $str_y) ((repr $x) (repr $y))
     (if (string< $str_x $str_y)
         ($x $y)
         ($y $x))))

; lookup_d: Look up if two variables are disjoint
; PeTTa adaptation: use tagged match
(= (lookup_d $kb-tag $x $y)
  (let ($x' $y') (orient_pair $x $y)
    (case (collapse (match &self ($kb-tag (DVar ($x' $y') $_ (Type "$d"))) found))
      (((found) True)
       (() False)))))

; dv_check: Check disjoint variable constraint
; Returns Error if constraint violated, () if ok
(= (dv_check $kb-tag $x $y)
  (if (or
        (== $x $y)
        (not (lookup_d $kb-tag $x $y)))
      (Error ($x $y) "Disjoint variable violation.")
      ()))

; check_dv_pairs: Check all pairs from two lists of variables
(= (check_dv_pairs $kb-tag $x_vars $y_vars)
  (map-atom $x_vars $x
    (map-atom $y_vars $y
      (dv_check $kb-tag $x $y))))

; lookup_subst: Look up token in substitution list
(= (lookup_subst $token $subst)
  (collapse (match-atom $subst ($token $val) $val)))

; check_dvs: Check DV constraints for substitution
; PeTTa adaptation: use lookup_subst helper and let* for readability
(= (check_dvs $kb-tag $subst $dvs0)
    (map-atom $dvs0 $d
      (let* ((($d1 $d2) $d)
             ($sub1 (lookup_subst $d1 $subst))
             ($sub2 (lookup_subst $d2 $subst))
             ($x_vars (find_vars $kb-tag $sub1))
             ($y_vars (find_vars $kb-tag $sub2)))
        (check_dv_pairs $kb-tag $x_vars $y_vars))))

; ===== Tests =====

!(println! "=== Testing Disjoint Variable Functions ===")
!(println! "")

!(println! "Test 1: map-pairs creates all pairs")
; Helper function for testing map-pairs
(= (make-pair $v1 $v2) ($v1 $v2))
!(test (collapse (map-pairs (a b) (x y) make-pair))
       ((((a x) (a y)) ((b x) (b y)))))

!(println! "Test 2: is_var identifies variables")
!(add-atom &self (KB2 (Var x 0 (Type "$v"))))
!(add-atom &self (KB2 (Var y 0 (Type "$v"))))
!(test (is_var KB2 x) True)
!(test (is_var KB2 y) True)
!(test (is_var KB2 z) False)

!(println! "Test 3: find_vars filters variables from statement")
!(add-atom &self (KB3 (Var ph 0 (Type "$v"))))
!(add-atom &self (KB3 (Var ps 0 (Type "$v"))))
!(test (find_vars KB3 (-> ph ps))
       (ph ps))

!(println! "Test 4: string< compares strings lexicographically")
!(test (string< a b) True)
!(test (string< b a) False)
!(test (string< x x) False)

!(println! "Test 5: orient_pair orders variables canonically")
!(test (orient_pair x y) (x y))
!(test (orient_pair y x) (x y))
!(test (orient_pair a z) (a z))

!(println! "Test 6: lookup_d finds disjoint variable pairs")
!(add-atom &self (KB6 (DVar (x y) 0 (Type "$d"))))
!(test (lookup_d KB6 x y) True)
!(test (lookup_d KB6 y x) True)
!(test (lookup_d KB6 x z) False)

!(println! "Test 7: dv_check validates disjoint constraints")
!(add-atom &self (KB7 (DVar (a b) 0 (Type "$d"))))
!(test (dv_check KB7 a b) ())
!(test (case (dv_check KB7 x x)
         (((Error $p $msg) (Error))
          ($_ not-error)))
       (Error))
!(test (case (dv_check KB7 c d)
         (((Error $p $msg) (Error))
          ($_ not-error)))
       (Error))

!(println! "Test 8: check_dv_pairs validates all pairs")
!(add-atom &self (KB8 (DVar (x y) 0 (Type "$d"))))
!(add-atom &self (KB8 (DVar (x z) 0 (Type "$d"))))
!(add-atom &self (KB8 (DVar (y z) 0 (Type "$d"))))
; All pairs disjoint - returns () for each check, nested by map-atom structure
!(test (collapse (check_dv_pairs KB8 (x y) (z)))
       (((()) (()))))

!(println! "Test 9: check_dvs validates substitution constraints")
!(add-atom &self (KB9 (Var ph 0 (Type "$v"))))
!(add-atom &self (KB9 (Var ps 0 (Type "$v"))))
!(add-atom &self (KB9 (Var ch 0 (Type "$v"))))
!(add-atom &self (KB9 (DVar (ph ps) 0 (Type "$d"))))
; Substitution: ph -> (wff x), ps -> (wff y)
; DV constraint: (ph ps) must remain disjoint
; Since x and y are not variables, find_vars returns empty, so check passes
!(test (check_dvs KB9 ((ph (wff x)) (ps (wff y))) ((ph ps)))
       (()))

!(println! "Test 10: Multiple orient_pair calls are consistent")
!(test (orient_pair b a) (a b))
!(test (orient_pair a b) (a b))
!(test (let ($x1 $y1) (orient_pair m n)
         (let ($x2 $y2) (orient_pair $x1 $y1)
           ($x2 $y2)))
       (m n))

!(println! "")
!(println! "=== All disjoint variable tests complete ===")
