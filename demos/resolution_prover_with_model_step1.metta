!(import! &self ../lib/lib_prolog)
!(import! &self ../lib/lib_he)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Resolution Theorem Prover - Model Extraction Step 1
;;;
;;; Step 1: Extract unit clauses as model when saturated
;;; When we saturate without finding empty clause, extract all unit clauses
;;; These represent forced assignments
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ID Counter using &self tagged atoms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (init-id-counter)
   (add-atom &self (id-counter 0)))

(= (next-id!)
   (match &self (id-counter $current)
     (let $next (+ $current 1)
       (let $_ (remove-atom &self (id-counter $current))
         (let $_ (add-atom &self (id-counter $next))
           $current)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Derivation Recording
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (record-deriv! $id $parent1-id $parent2-id)
   (add-atom &self (deriv $id $parent1-id $parent2-id)))

(= (record-axiom! $id $lits)
   (let $_ (add-atom &self (deriv $id axiom axiom))
     (add-atom &self (clause-lits $id $lits))))

(= (record-unit-deriv! $id $parent-id)
   (add-atom &self (deriv $id unit $parent-id)))

(= (get-deriv $id)
   (match &self (deriv $id $p1 $p2)
     (deriv $id $p1 $p2)))

(= (collect-proof-ids $id)
   (match &self (deriv $id $p1 $p2)
     (collect-proof-ids-inner $id $p1 $p2)))

(= (collect-proof-ids-inner $id axiom axiom)
   (Cons $id Nil))

(= (collect-proof-ids-inner $id unit $parent)
   (Cons $id (collect-proof-ids $parent)))

(= (collect-proof-ids-inner $id $p1 $p2)
   (Cons $id (append-lits (collect-proof-ids $p1) (collect-proof-ids $p2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Model Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extract all unit clauses from clause set
;; These represent forced literal assignments
(= (extract-units Nil) Nil)
(= (extract-units (Cons $clause $rest))
   (let $lits (get-lits $clause)
     (if (== (list-length $lits) 1)
         (Cons (get-first-lit $lits) (extract-units $rest))
         (extract-units $rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Literals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (complementary $lit1 $lit2)
   (case ($lit1 $lit2) ((((lit $x) (nlit $x)) True)
                         (((nlit $x) (lit $x)) True)
                         ($_ False))))

(= (complement-of (lit $x)) (nlit $x))
(= (complement-of (nlit $x)) (lit $x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; List Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (member? $x Nil) False)
(= (member? $x (Cons $x $tail)) True)
(= (member? $x (Cons $head $tail))
   (member? $x $tail))

(= (remove-lit $lit Nil) Nil)
(= (remove-lit $lit (Cons $lit $tail)) $tail)
(= (remove-lit $lit (Cons $head $tail))
   (Cons $head (remove-lit $lit $tail)))

(= (append-lits Nil $l2) $l2)
(= (append-lits (Cons $head $tail) $l2)
   (Cons $head (append-lits $tail $l2)))

(= (list-length Nil) 0)
(= (list-length (Cons $h $t)) (+ 1 (list-length $t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Clause Operations with IDs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (get-id (c $id $lits)) $id)
(= (get-lits (c $id $lits)) $lits)
(= (is-empty (c $id Nil)) True)
(= (is-empty (c $id (Cons $head $tail))) False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Clause Simplification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (has-complement $lit Nil) False)
(= (has-complement $lit (Cons $head $tail))
   (if (== $head (complement-of $lit))
       True
       (has-complement $lit $tail)))

(= (is-tautology Nil) False)
(= (is-tautology (Cons $lit $rest))
   (if (== (has-complement $lit $rest) True)
       True
       (is-tautology $rest)))

(= (is-subset-of Nil $c2) True)
(= (is-subset-of (Cons $head $tail) $c2)
   (if (== (member? $head $c2) True)
       (is-subset-of $tail $c2)
       False))

(= (is-subsumed-by $clause Nil) False)
(= (is-subsumed-by $clause (Cons $first $rest))
   (if (== (is-empty $clause) True)
       False
       (if (== (is-empty $first) True)
           (is-subsumed-by $clause $rest)
           (if (== (get-lits $clause) (get-lits $first))
               (is-subsumed-by $clause $rest)
               (if (== (is-subset-of (get-lits $first) (get-lits $clause)) True)
                   True
                   (is-subsumed-by $clause $rest))))))

(= (filter-subsumed Nil $all) Nil)
(= (filter-subsumed (Cons $clause $rest) $all)
   (if (== (is-subsumed-by $clause $all) True)
       (filter-subsumed $rest $all)
       (Cons $clause (filter-subsumed $rest $all))))

(= (simplify-clauses $clauses)
   (filter-subsumed $clauses $clauses))

(= (simplify $clauses) (simplify-clauses $clauses))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Unit Propagation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (find-unit Nil) (no-unit))
(= (find-unit (Cons $clause $rest))
   (if (== (list-length (get-lits $clause)) 1)
       (unit (get-first-lit (get-lits $clause)))
       (find-unit $rest)))

(= (get-first-lit (Cons $lit $rest)) $lit)
(= (get-first-lit Nil) (no-lit))

(= (apply-unit $lit Nil) Nil)
(= (apply-unit $lit (Cons $clause $rest))
   (let $lits (get-lits $clause)
     (if (== (member? (complement-of $lit) $lits) True)
         (let $reduced (remove-lit (complement-of $lit) $lits)
           (let $new-id (next-id!)
             (let $_ (record-unit-deriv! $new-id (get-id $clause))
               (Cons (c $new-id $reduced) (apply-unit $lit $rest)))))
         (if (== (member? $lit $lits) True)
             (apply-unit $lit $rest)
             (Cons $clause (apply-unit $lit $rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (try-resolve-lit $lit1 Nil $c1 $c2) (no-resolvent))
(= (try-resolve-lit $lit1 (Cons $lit2 $rest2) $c1 $c2)
   (if (== (complementary $lit1 $lit2) True)
       (let $rem1 (remove-lit $lit1 (get-lits $c1))
         (let $rem2 (remove-lit $lit2 (get-lits $c2))
           (let $resolvent (append-lits $rem1 $rem2)
             (if (== (is-tautology $resolvent) True)
                 (no-resolvent)
                 (let $new-id (next-id!)
                   (let $_ (record-deriv! $new-id (get-id $c1) (get-id $c2))
                     (c $new-id $resolvent)))))))
       (try-resolve-lit $lit1 $rest2 $c1 $c2)))

(= (resolve-loop Nil $c2lits $c1 $c2) (no-resolvent))
(= (resolve-loop (Cons $lit1 $rest1) $c2lits $c1 $c2)
   (let $result (try-resolve-lit $lit1 $c2lits $c1 $c2)
     (if (== $result (no-resolvent))
         (resolve-loop $rest1 $c2lits $c1 $c2)
         $result)))

(= (resolve $c1 $c2)
   (resolve-loop (get-lits $c1) (get-lits $c2) $c1 $c2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Clause Set Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (is-empty-list Nil) True)
(= (is-empty-list (Cons $head $tail)) False)

(= (contains-empty-once $clauses)
   (once (contains-empty $clauses)))

(= (contains-empty Nil) False)
(= (contains-empty (Cons $clause $rest))
   (if (== (is-empty $clause) True)
       True
       (contains-empty $rest)))

;; Find and return the empty clause (not just True/False)
(= (find-empty-clause Nil) (no-empty))
(= (find-empty-clause (Cons $clause $rest))
   (if (== (is-empty $clause) True)
       $clause
       (find-empty-clause $rest)))

(= (append-sets Nil $set) $set)
(= (append-sets (Cons $head $tail) $set)
   (Cons $head (append-sets $tail $set)))

(= (resolve-against-all $clause Nil) Nil)
(= (resolve-against-all $clause (Cons $other $rest))
   (if (== $clause $other)
       (resolve-against-all $clause $rest)
       (let $resolvent (resolve $clause $other)
         (if (== $resolvent (no-resolvent))
             (resolve-against-all $clause $rest)
             (Cons $resolvent (resolve-against-all $clause $rest))))))

(= (resolve-all-pairs Nil $all-clauses) Nil)
(= (resolve-all-pairs (Cons $clause $rest) $all-clauses)
   (let $resolvents (resolve-against-all $clause $all-clauses)
     (append-sets $resolvents (resolve-all-pairs $rest $all-clauses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Main Prover Loop - NOW RETURNS MODEL ON SATURATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (wrap-clause-with-id $lits)
   (let $id (next-id!)
     (let $_ (record-axiom! $id $lits)
       (c $id $lits))))

(= (wrap-clauses Nil) Nil)
(= (wrap-clauses (Cons $lits $rest))
   (Cons (wrap-clause-with-id $lits) (wrap-clauses $rest)))

(= (prove-once $clauses $max-iter)
   (let $_ (init-id-counter)
     (let $clauses-with-ids (wrap-clauses $clauses)
       (once (prove-inner $clauses-with-ids $clauses-with-ids $max-iter)))))

(= (prove $clauses $max-iter)
   (prove-inner $clauses $clauses $max-iter))

(= (prove-inner $clauses $all-seen $remaining)
   (let $unit-check (find-unit $clauses)
     (if (== $unit-check (unit $lit))
         (let $after-unit (apply-unit $lit $clauses)
           (prove-inner $after-unit $all-seen $remaining))
         (prove-step $clauses $all-seen $remaining))))

(= (prove-step $clauses $all-seen $remaining)
   (if (== (contains-empty-once $clauses) True)
       ;; Found empty clause - return its ID for proof extraction
       (let $empty-clause (find-empty-clause $clauses)
         (unsat (get-id $empty-clause) (- 10 $remaining)))
       (if (<= $remaining 0)
           (max-iterations 0)
           (let $size (list-length $clauses)
             (if (> $size 300)
                 (size-limit-exceeded $size)
                 (let $new-clauses (resolve-all-pairs $clauses $clauses)
                   (let $simplified (simplify $new-clauses)
                     (if (== $simplified Nil)
                         ;; SATURATED - Extract model from remaining clauses
                         (sat (extract-units $clauses))
                         (prove-inner
                           (append-sets $clauses $simplified)
                           (append-sets $all-seen $simplified)
                           (- $remaining 1))))))))))
