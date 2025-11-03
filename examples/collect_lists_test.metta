!(println! "collect-lists-test-start")
!(bind! &kb (new-space))

(: append (-> (List $a) (List $a) (List $a)))
(= (append Nil $list) $list)
(= (append (Cons $head $tail) $list)
   (Cons $head (append $tail $list)))

(: matchc (-> SpaceType Atom Atom %Undefined%))
(= (matchc $space $pattern $query)
   (collapse (match $space $pattern $query)))

(: match-atom (-> Expression Atom Atom %Undefined$))
(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (let $pattern $head $rewrite)
       (empty))))
(= (match-atom $expr $pattern $rewrite)
   (chain (decons-atom $expr) $ht
     (unify ($head $tail) $ht
       (match-atom $tail $pattern $rewrite)
       (empty))))

(: match-atom' (-> Expression Atom Atom %Undefined$))
(= (match-atom' $expr $pattern $rewrite)
   (case (match-atom $expr $pattern $rewrite)
     ((Empty ()) ($q $q))))

(: match-atom'' (-> Expression Atom Atom Atom %Undefined$))
(= (match-atom'' $expr $pattern $rewrite $Empty)
   (case (match-atom $expr $pattern $rewrite)
     ((Empty $Empty) ($q $q))))

(: collect_lists_by_depth (-> (List Atom) Number Number (List Atom) (List Atom)))
(= (collect_lists_by_depth $unordered_list $current $max $ordered_list)
  (if (> $current $max)
      $ordered_list
      (let $current_list (match-atom'' $unordered_list ($current $list) $list Nil)
        (collect_lists_by_depth $unordered_list (+ 1 $current) $max (append $ordered_list $current_list)))))

(: max-atom (-> (List Number) Number))
(= (max-atom (Cons $head Nil) $head))
(= (max-atom (Cons $head $tail)
   (let $rest (max-atom $tail)
     (if (> $head $rest) $head $rest))))

(: pairs->levels (-> (List Atom) (List Number)))
(= (pairs->levels $pairs)
   (collapse (match-atom' $pairs ((FSDepth $l) $_) $l)))

(: pairs->max (-> (List Atom) Number))
(= (pairs->max $pairs)
   (pairs->max_aux (pairs->levels $pairs)))

(: pairs->max_aux (-> (List Number) Number))
(= (pairs->max_aux ()) 0)
(= (pairs->max_aux $levels) (max-atom $levels))

!(add-atom &kb (FList (FSDepth 1) (Cons (Cons "term" "t") (Cons (Cons "term" "r") Nil))))
!(add-atom &kb (FList (FSDepth 2) (Cons (Cons "term" "s") Nil)))
!(add-atom &kb (FList (FSDepth 3) (Cons (Cons "wff" "P") (Cons (Cons "wff" "Q") Nil))))

!(println! ("atoms" (collapse (get-atoms &kb))))
!(println! ("match-depth" (matchc &kb (FList $depth $items) $depth)))
!(println! ("match-const" (matchc &kb (FList (FSDepth 1) $items) $items)))
!(println! ("match-var" (matchc &kb (FList (FSDepth $level) $items) ((FSDepth $level) $items))))
!(println! ("pairs" (matchc &kb (FList (FSDepth $level) $items) ((FSDepth $level) $items))))
!(println! ("levels" (pairs->levels (matchc &kb (FList (FSDepth $level) $items) ((FSDepth $level) $items)))))
!(println! ("ordered"
            (collect_lists_by_depth
              (matchc &kb (FList (FSDepth $level) $items) ((FSDepth $level) $items))
              1
              (pairs->max (matchc &kb (FList (FSDepth $level) $items) ((FSDepth $level) $items)))
              Nil)))

!(println! "collect-lists-test-end")
