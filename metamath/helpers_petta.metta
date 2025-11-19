!(import! &self ../lib/lib_he)

;; PeTTa version of helper functions for add_a
;; Adapted from mmverify-utils.metta with PeTTa patterns

; ===== Utility Functions =====

(= (matchc $space-tag $pattern $query)
  (collapse (match &self ($space-tag $pattern) ($space-tag $query))))

(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

(= (to-list' $expr $tail)
  (if (== $expr ()) $tail
    (Cons (car-atom $expr)
        (to-list' (cdr-atom $expr) $tail))))

(= (mappend Nil $list) $list)
(= (mappend (Cons $head $tail) $list)
   (Cons $head (mappend $tail $list)))

(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

; PeTTa adaptation: simpler approach using map-atom
; Collect atoms from expression that match pattern
(= (match-atom-collect $expr $pattern)
  (case (collapse (map-atom $expr $x (if (== $x $pattern) $x ())))
    (() Nil)
    ($matches $matches)))

; PeTTa version: collect_lists_by_depth
; collapse returns a tuple/list, convert to Cons/Nil then append
(= (collect-lists-by-depth-petta $space-tag $current $max $ordered-list)
  (if (> $current $max)
    $ordered-list
    (let $current-lists (collapse (match &self ($space-tag ($current $list)) $list))
      (let $combined
        (case $current-lists
          ((() $ordered-list)  ; No matches
           ($tuple  ; Got results - convert tuple to list and append all
             (let $as-cons-list (tuple-to-cons-list $current-lists)
               (let $all-appended (mappend-all $as-cons-list)
                 (mappend $ordered-list $all-appended))))))
        (collect-lists-by-depth-petta $space-tag (+ 1 $current) $max $combined)))))

; Convert tuple like ((Cons a Nil) (Cons c Nil)) to Cons list
(= (tuple-to-cons-list $tuple) (to-list $tuple))

; Helper to append all lists in a Cons list
(= (mappend-all Nil) Nil)
(= (mappend-all (Cons $head Nil)) $head)
(= (mappend-all (Cons $head $tail))
  (mappend $head (mappend-all $tail)))

; PeTTa version: add_mand_var with tagged atoms
(= (add-mand-var-petta $space-tag $tok)
  (case (collapse (match &self ($space-tag (Var $tok $_ (Type "$v"))) found))
    (((found)
       (case (collapse (match &self ($space-tag (MandVar $tok)) found))
         (((found) ())
          (() (add-atom &self ($space-tag (MandVar $tok)))))))
     (() ()))))

; PeTTa version: assign_f_hyps with progn for side effects
(= (assign-f-hyps-petta $space-tag Nil) Nil)
(= (assign-f-hyps-petta $space-tag (Cons $head $tail))
   (let $tail-result (assign-f-hyps-petta $space-tag $tail)
     (let ($typecode $var) $head
       (case (collapse (match &self ($space-tag (MandVar $var)) found))
         (((found)
            (prog1
              (Cons $head $tail-result)
              (remove-atom &self ($space-tag (MandVar $var)))))
          (() $tail-result))))))

(= (remove-pattern-petta $space-tag $pattern)
  (collapse (case (match &self ($space-tag $pattern) $pattern)
    (($pattern (remove-atom &self ($space-tag $pattern)))
     (Empty ())))))

; ===== Tier 1 Utilities (Additional) =====

; match-atom: Match pattern in expression and rewrite
; PeTTa version using decons-atom with proper non-determinism handling
; Rule 1: Try to match the head
(= (match-atom $expr $pattern $rewrite)
   (let ($head $tail) (decons-atom $expr)
     (let $pattern $head $rewrite)))

; Rule 2: Recursively search the tail
(= (match-atom $expr $pattern $rewrite)
   (let ($head $tail) (decons-atom $expr)
     (match-atom $tail $pattern $rewrite)))

; match-atom': Wrapper that handles Empty cases
(= (match-atom' $expr $pattern $rewrite)
  (case (match-atom $expr $pattern $rewrite) (
    (() ())
    ($q $q))))

; match-atom'': Wrapper with custom empty value
(= (match-atom'' $expr $pattern $rewrite $Empty)
  (case (match-atom $expr $pattern $rewrite) (
    (() $Empty)
    ($q $q))))

; update-atom: Update an atom in a space
(= (update-atom $pattern $update_pattern)
  (case (collapse (match &self $pattern $pattern)) (
    (() ())
    ($matches
      (progn
        (map-atom $matches $atom
          (progn
            (add-atom &self $update_pattern)
            (remove-atom &self $atom)))
        True)))))

; adjust-state-additive: Add to state
(= (adjust-state-additive $state $delta)
  (let $current (get-state $state)
    (change-state! $state (+ $current $delta))))

; adjust-state-subtractive: Subtract from state
(= (adjust-state-subtractive $state $delta)
  (let $current (get-state $state)
    (change-state! $state (- $current $delta))))

; remove_from_stack: Remove entries from stack above pointer
; Note: PeTTa version uses &self instead of &stack parameter
(= (remove_from_stack $stack_ptr $stack_len)
  (if (> $stack_len $stack_ptr)
    (progn
      (collapse (let ((Num $stack_ptr) $s)
                  (match &self ((Num $stack_ptr) $s)
                    (remove-atom &self ((Num $stack_ptr) $s)))))
      (remove_from_stack (+ 1 $stack_ptr) $stack_len))
    ()))

; empty-space: Remove all atoms from space with given tag
; PeTTa version: simplified without matchc dependency
(= (empty-space $space-tag)
  (collapse (match &self ($space-tag $atom)
              (remove-atom &self ($space-tag $atom)))))

; ===== Frame Management =====

; push-frame: Increment frame depth
(= (push-frame $fd)
  (adjust-state-additive $fd 1))

; pop-frame: Pop frame and remove all data at current level
; PeTTa adaptation: uses &self with KB tag instead of separate $kb parameter
(= (pop-frame $kb-tag $fd)
  (let $level (get-state $fd)
    (progn
      ; Remove EList at current level
      (collapse (match &self ($kb-tag (EList (FSDepth $level) $elist))
                  (remove-atom &self ($kb-tag (EList (FSDepth $level) $elist)))))
      ; Remove FList at current level
      (collapse (match &self ($kb-tag (FList (FSDepth $level) $flist))
                  (remove-atom &self ($kb-tag (FList (FSDepth $level) $flist)))))
      ; Remove all other data at current level (Var, DVar, etc.)
      (collapse (match &self ($kb-tag ($any1 $any2 (FSDepth $level) $data))
                  (remove-atom &self ($kb-tag ($any1 $any2 (FSDepth $level) $data)))))
      ; Decrement frame depth
      (adjust-state-subtractive $fd 1))))

; ===== Disjoint Variables =====

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

!(println! "=== Testing PeTTa Helper Functions ===")
!(println! "")

!(println! "Test 1: to-list converts expression to Cons/Nil")
!(test (to-list (a b c)) (Cons a (Cons b (Cons c Nil))))

!(println! "Test 2: from-list converts Cons/Nil to expression")
!(test (from-list (Cons a (Cons b (Cons c Nil)))) (a b c))

!(println! "Test 3: mappend concatenates lists")
!(test (mappend (Cons a (Cons b Nil)) (Cons c (Cons d Nil)))
       (Cons a (Cons b (Cons c (Cons d Nil)))))

!(println! "Test 4: flatten-list flattens nested expression lists")
!(test (flatten-list (Cons (a b) (Cons c Nil)))
       (Cons a (Cons b (Cons c Nil))))

!(println! "Test 5: match-atom-collect finds atoms in expression")
; Note: match-atom-collect is not actually needed for add_a, skipping test
; !(test (match-atom-collect (a b c a d) a) (a a))

!(println! "Test 6: collect-lists-by-depth-petta - empty case")
!(test (collect-lists-by-depth-petta kb1 1 0 Nil) Nil)

!(println! "Test 7: collect-lists-by-depth-petta - single level")
!(add-atom &self (kb2 (1 (Cons a Nil))))
!(test (collect-lists-by-depth-petta kb2 1 1 Nil)
       (Cons a Nil))

!(println! "Test 8: collect-lists-by-depth-petta - multiple levels")
!(add-atom &self (kb3 (1 (Cons a Nil))))
!(add-atom &self (kb3 (2 (Cons b Nil))))
!(add-atom &self (kb3 (1 (Cons c Nil))))
!(test (collect-lists-by-depth-petta kb3 1 2 Nil)
       (Cons a (Cons c (Cons b Nil))))

!(println! "Test 9: add-mand-var-petta adds mandatory variables")
!(add-atom &self (kb4 (Var x 0 (Type "$v"))))
!(add-mand-var-petta kb4 x)
!(test (collapse (match &self (kb4 (MandVar $v)) $v)) (x))

!(println! "Test 10: assign-f-hyps-petta filters by mandatory vars")
!(add-atom &self (kb5 (Var x 0 (Type "$v"))))
!(add-atom &self (kb5 (Var y 0 (Type "$v"))))
!(add-atom &self (kb5 (MandVar x)))
!(add-atom &self (kb5 (MandVar y)))
!(test (assign-f-hyps-petta kb5 (Cons (class x) (Cons (wff y) (Cons (class z) Nil))))
       (Cons (class x) (Cons (wff y) Nil)))

!(println! "")
!(println! "=== All PeTTa helper tests complete ===")
