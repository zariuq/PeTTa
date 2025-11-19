!(import! &self ../lib/lib_he)

;; PeTTa version of add_a and make_assertion
;; Adapted from mmverify-utils.metta with PeTTa patterns

; Import all helper functions inline (from helpers_petta.metta)

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

(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

(= (tuple-to-cons-list $tuple) (to-list $tuple))

(= (mappend-all Nil) Nil)
(= (mappend-all (Cons $head Nil)) $head)
(= (mappend-all (Cons $head $tail))
  (mappend $head (mappend-all $tail)))

(= (collect-lists-by-depth-petta $space-tag $current $max $ordered-list)
  (if (> $current $max)
    $ordered-list
    (let $current-lists (collapse (match &self ($space-tag ($current $list)) $list))
      (let $combined
        (case $current-lists
          ((() $ordered-list)
           ($tuple (let $as-cons-list (tuple-to-cons-list $current-lists)
               (let $all-appended (mappend-all $as-cons-list)
                 (mappend $ordered-list $all-appended))))))
        (collect-lists-by-depth-petta $space-tag (+ 1 $current) $max $combined)))))

(= (add-mand-var-petta $space-tag $tok)
  (case (collapse (match &self ($space-tag (Var $tok $_ (Type "$v"))) found))
    (((found)
       (case (collapse (match &self ($space-tag (MandVar $tok)) found))
         (((found) ())
          (() (add-atom &self ($space-tag (MandVar $tok)))))))
     (() ()))))

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

; Define max-atom for PeTTa (not built-in like in HE)
(= (max-atom-petta Nil) 0)
(= (max-atom-petta (Cons $head Nil)) $head)
(= (max-atom-petta (Cons $head $tail))
  (let $max-tail (max-atom-petta $tail)
    (if (> $head $max-tail) $head $max-tail)))

; Helper to get max from a tuple
(= (max-from-tuple $tuple)
  (case $tuple
    (() 0)
    ($t (max-atom-petta (to-list $t)))))

; PeTTa version of make_assertion
(= (make-assertion-petta $space-tag $stmt)
  (let $e-hyps-lists (matchc $space-tag (EList (FSDepth $level) $elist) ($level $elist))
    (let $e-levels (collapse (map-atom $e-hyps-lists $pair
        (let ($l $_) $pair $l)))
      (let $e-max-level (max-from-tuple $e-levels)
        (let $e-hyps-list (collect-lists-by-depth-petta $space-tag 1 $e-max-level Nil)
          (let $e-hyps-toks (from-list $e-hyps-list)
            (prog1
              ; Build and return the assertion data
              (let $mand-vars (matchc $space-tag (MandVar $var) $var)
                (let $dvs (matchc $space-tag (DVar ($x $y) $_ (Type "$d"))
                    (case (collapse (match &self ($space-tag (MandVar $x)) found))
                      (((found)
                         (case (collapse (match &self ($space-tag (MandVar $y)) found))
                           (((found) ($x $y))
                            (() ()))))
                       (() ()))))
                  (let $f-hyps-lists (matchc $space-tag (FList (FSDepth $level) $flist) ($level $flist))
                    (let $f-levels (collapse (map-atom $f-hyps-lists $pair
                        (let ($l $_) $pair $l)))
                      (let $f-max-level (max-from-tuple $f-levels)
                        (let $f-hyps-list (collect-lists-by-depth-petta $space-tag 1 $f-max-level Nil)
                          (let $f-hyps (assign-f-hyps-petta $space-tag $f-hyps-list)
                            ((DVars $dvs) (FHyps (from-list $f-hyps)) (EHyps (from-list $e-hyps-list)) (Statement $stmt)))))))))
              ; Side effects
              (map-atom $e-hyps-toks $tok (add-mand-var-petta $space-tag $tok))
              (map-atom $stmt $tok (add-mand-var-petta $space-tag $tok))
              (remove-pattern-petta $space-tag (MandVar $_)))))))))

; PeTTa version of add_a
(= (add-a-petta $space-tag $label $stmt)
  (let ((DVars $dvs) (FHyps $f-hyps) (EHyps $e-hyps) (Statement $stmt))
      (make-assertion-petta $space-tag $stmt)
    (add-atom &self ($space-tag ((Label $label) Assertion ((DVars $dvs) (FHyps $f-hyps) (EHyps $e-hyps) (Statement $stmt) (Type "$a")))))))

; ===== Tests =====

!(println! "=== Testing PeTTa add_a ===")
!(println! "")

!(println! "Test 1: Simple assertion with no hypotheses")
!(add-a-petta kb1 ax1 (wff P))
!(test (collapse (match &self (kb1 ((Label $l) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a")))) ($l $s)))
       ((ax1 (wff P))))

!(println! "Test 2: Assertion with floating hypothesis (x in statement)")
!(add-atom &self (kb2 (Var x 0 (Type "$v"))))
!(add-atom &self (kb2 (FList (FSDepth 1) (Cons (class x) Nil))))
!(add-a-petta kb2 ax2 (wff x))
!(test (collapse (match &self (kb2 ((Label ax2) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a")))) $fh))
       (((class x))))

!(println! "Test 3: Assertion with essential hypothesis")
!(add-atom &self (kb3 (EList (FSDepth 1) (Cons (wff P) Nil))))
!(add-a-petta kb3 ax3 (wff (implies P Q)))
!(test (collapse (match &self (kb3 ((Label ax3) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a")))) $eh))
       (((wff P))))

!(println! "Test 4: Assertion with disjoint variables (x, y in statement)")
!(add-atom &self (kb4 (Var x 0 (Type "$v"))))
!(add-atom &self (kb4 (Var y 0 (Type "$v"))))
!(add-atom &self (kb4 (DVar (x y) 1 (Type "$d"))))
!(add-atom &self (kb4 (FList (FSDepth 1) (Cons (class x) (Cons (class y) Nil)))))
!(add-a-petta kb4 ax4 (wff x y))
!(test (collapse (match &self (kb4 ((Label ax4) Assertion ((DVars $dv) (FHyps $fh) (EHyps $eh) (Statement $s) (Type "$a")))) $dv))
       (((x y))))

!(println! "")
!(println! "=== All PeTTa add_a tests complete ===")
