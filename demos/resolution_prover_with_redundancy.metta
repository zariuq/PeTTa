!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Resolution Theorem Prover with Better Redundancy Elimination
;;;
;;; Implements:
;;; - Forward subsumption (don't add subsumed clauses)
;;; - Backward subsumption (remove subsumed existing clauses)
;;; - Set-based clause comparison
;;; - Clause size limits
;;;
;;; OPTIMIZED: Uses separate spaces for better Prolog indexing:
;;; - &counter: ID counter (hot path, frequently updated)
;;; - &deriv: Derivation records (write-once, read for proof reconstruction)
;;; - &clauses: Clause literals storage (write-once, rarely read)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ID Counter using &counter space (optimized for hot path)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (init-id-counter)
   (let $_ (once (clear-id-counter))
     (add-atom &counter (id-counter 0))))

(= (clear-id-counter)
   (unify (match &counter (id-counter $n) $n)
          $val
          (remove-atom &counter (id-counter $val))
          True))

(= (next-id!)
   (match &counter (id-counter $current)
     (let $next (+ $current 1)
       (let $_ (remove-atom &counter (id-counter $current))
         (let $_ (add-atom &counter (id-counter $next))
           $current)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Derivation Recording using &deriv and &clauses spaces
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (record-deriv! $id $lits $parent1-id $parent2-id)
   (let $_ (add-atom &deriv (deriv $id $parent1-id $parent2-id))
     (add-atom &clauses (clause-lits $id $lits))))

(= (record-axiom! $id $lits)
   (let $_ (add-atom &deriv (deriv $id axiom axiom))
     (add-atom &clauses (clause-lits $id $lits))))

(= (get-deriv $id)
   (match &deriv (deriv $id $p1 $p2)
     (deriv $id $p1 $p2)))

(= (collect-proof-ids $id)
   (match &deriv (deriv $id $p1 $p2)
     (collect-proof-ids-inner $id $p1 $p2)))

(= (collect-proof-ids-inner $id axiom axiom)
   (Cons $id Nil))

(= (collect-proof-ids-inner $id $p1 $p2)
   (Cons $id (append-lits (collect-proof-ids $p1) (collect-proof-ids $p2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Literals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (complementary $lit1 $lit2)
   (case ($lit1 $lit2) ((((lit $x) (nlit $x)) True)
                         (((nlit $x) (lit $x)) True)
                         ($_ False))))

(= (complement-of (lit $x)) (nlit $x))
(= (complement-of (nlit $x)) (lit $x))

;;; Literal ordering for normalization
(= (lit-less-than (lit $x) (lit $y)) (< $x $y))
(= (lit-less-than (lit $x) (nlit $y)) True)
(= (lit-less-than (nlit $x) (lit $y)) False)
(= (lit-less-than (nlit $x) (nlit $y)) (< $x $y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; List Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (member? $x Nil) False)
(= (member? $x (Cons $head $tail))
   (if (== $x $head)
       True
       (member? $x $tail)))

(= (remove-lit $lit Nil) Nil)
(= (remove-lit $lit (Cons $head $tail))
   (if (== $lit $head)
       $tail
       (Cons $head (remove-lit $lit $tail))))

(= (append-lits Nil $l2) $l2)
(= (append-lits (Cons $head $tail) $l2)
   (Cons $head (append-lits $tail $l2)))

(= (list-length Nil) 0)
(= (list-length (Cons $h $t)) (+ 1 (list-length $t)))

;;; Insert literal in sorted position
(= (insert-sorted $lit Nil) (Cons $lit Nil))
(= (insert-sorted $lit (Cons $head $tail))
   (if (lit-less-than $lit $head)
       (Cons $lit (Cons $head $tail))
       (if (== $lit $head)
           (Cons $head $tail)  ; Don't duplicate
           (Cons $head (insert-sorted $lit $tail)))))

;;; Sort literals for canonical form
(= (sort-lits Nil) Nil)
(= (sort-lits (Cons $lit $rest))
   (insert-sorted $lit (sort-lits $rest)))

;;; Remove duplicates from sorted list
(= (remove-dups-sorted Nil) Nil)
(= (remove-dups-sorted (Cons $x Nil)) (Cons $x Nil))
(= (remove-dups-sorted (Cons $x (Cons $y $rest)))
   (if (== $x $y)
       (remove-dups-sorted (Cons $y $rest))
       (Cons $x (remove-dups-sorted (Cons $y $rest)))))

;;; Normalize clause: sort and remove duplicates
(= (normalize-lits $lits)
   (remove-dups-sorted (sort-lits $lits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Clause Operations with IDs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (get-id (c $id $lits)) $id)
(= (get-lits (c $id $lits)) $lits)
(= (is-empty (c $id Nil)) True)
(= (is-empty (c $id (Cons $head $tail))) False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Clause Simplification and Redundancy
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

;;; Check if first list is subset of second (for subsumption)
(= (is-subset-of Nil $c2) True)
(= (is-subset-of (Cons $head $tail) $c2)
   (if (== (member? $head $c2) True)
       (is-subset-of $tail $c2)
       False))

;;; Check if clause is subsumed by any clause in list
(= (is-subsumed-by $clause Nil) False)
(= (is-subsumed-by $clause (Cons $other $rest))
   (if (== (get-id $clause) (get-id $other))
       (is-subsumed-by $clause $rest)  ; Don't self-subsume
       (if (== (is-subset-of (get-lits $other) (get-lits $clause)) True)
           True
           (is-subsumed-by $clause $rest))))

;;; Forward subsumption: Filter out clauses subsumed by existing
(= (forward-subsume Nil $existing) Nil)
(= (forward-subsume (Cons $clause $rest) $existing)
   (if (== (is-subsumed-by $clause $existing) True)
       (forward-subsume $rest $existing)
       (Cons $clause (forward-subsume $rest $existing))))

;;; Backward subsumption: Remove existing clauses subsumed by new
(= (backward-subsume $existing Nil) $existing)
(= (backward-subsume $existing (Cons $new-clause $rest))
   (let $filtered (filter-not-subsumed-by $existing $new-clause)
     (backward-subsume $filtered $rest)))

(= (filter-not-subsumed-by Nil $subsumer) Nil)
(= (filter-not-subsumed-by (Cons $clause $rest) $subsumer)
   (if (== (is-subset-of (get-lits $subsumer) (get-lits $clause)) True)
       (filter-not-subsumed-by $rest $subsumer)
       (Cons $clause (filter-not-subsumed-by $rest $subsumer))))

;;; Combined redundancy elimination
;;; Returns (kept-new . updated-existing) as a pair
(= (eliminate-redundancy $new-clauses $existing)
   (let $non-taut (filter-non-tautologies $new-clauses)
     (let $forward (forward-subsume $non-taut $existing)
       (let $backward (backward-subsume $existing $forward)
         (Cons $forward $backward)))))

(= (filter-non-tautologies Nil) Nil)
(= (filter-non-tautologies (Cons $clause $rest))
   (if (== (is-tautology (get-lits $clause)) True)
       (filter-non-tautologies $rest)
       (Cons $clause (filter-non-tautologies $rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution with Normalization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (try-resolve-lit $lit1 Nil $c1 $c2) (no-resolvent))
(= (try-resolve-lit $lit1 (Cons $lit2 $rest2) $c1 $c2)
   (if (== (complementary $lit1 $lit2) True)
       (let $rem1 (remove-lit $lit1 (get-lits $c1))
         (let $rem2 (remove-lit $lit2 (get-lits $c2))
           (let $merged (append-lits $rem1 $rem2)
             (let $normalized (normalize-lits $merged)  ; Sort and dedup
               (if (== (is-tautology $normalized) True)
                   (no-resolvent)
                   (if (> (list-length $normalized) 10)  ; Size limit
                       (no-resolvent)
                       (let $new-id (next-id!)
                         (let $_ (record-deriv! $new-id $normalized (get-id $c1) (get-id $c2))
                           (c $new-id $normalized)))))))))
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
;;; Resolution with Redundancy Control
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (resolve-against-all $clause Nil) Nil)
(= (resolve-against-all $clause (Cons $other $rest))
   (if (< (get-id $clause) (get-id $other))
       (let $resolvent (resolve $clause $other)
         (if (== $resolvent (no-resolvent))
             (resolve-against-all $clause $rest)
             (Cons $resolvent (resolve-against-all $clause $rest))))
       (resolve-against-all $clause $rest)))

(= (resolve-all-pairs Nil $all-clauses) Nil)
(= (resolve-all-pairs (Cons $clause $rest) $all-clauses)
   (let $resolvents (resolve-against-all $clause $all-clauses)
     (append-lits $resolvents (resolve-all-pairs $rest $all-clauses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Main Prover Loop with Better Redundancy
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (contains-empty Nil) False)
(= (contains-empty (Cons $clause $rest))
   (if (== (is-empty $clause) True)
       True
       (contains-empty $rest)))

(= (find-empty-clause Nil) (no-empty))
(= (find-empty-clause (Cons $clause $rest))
   (if (== (is-empty $clause) True)
       $clause
       (find-empty-clause $rest)))

(= (wrap-clause-with-id $lits)
   (let $normalized (normalize-lits $lits)
     (let $id (next-id!)
       (let $_ (record-axiom! $id $normalized)
         (c $id $normalized)))))

(= (wrap-clauses Nil) Nil)
(= (wrap-clauses (Cons $lits $rest))
   (Cons (wrap-clause-with-id $lits) (wrap-clauses $rest)))

(= (my-car (Cons $x $rest)) $x)
(= (my-cdr (Cons $x $rest)) $rest)

(= (prove-once $clauses $max-iter)
   (let $_ (init-id-counter)
     (let $wrapped (once (wrap-clauses $clauses))
       (once (prove-loop $wrapped $max-iter)))))

(= (prove-loop $clauses $remaining)
   (if (== (contains-empty $clauses) True)
       (let $empty (find-empty-clause $clauses)
         (unsat (get-id $empty) $remaining))
       (if (<= $remaining 0)
           (max-iterations 0)
           (if (> (list-length $clauses) 10000)  ; Clause set size limit (increased)
               (size-limit-exceeded (list-length $clauses))
               (let $new (once (resolve-all-pairs $clauses $clauses))
                 (let $result (eliminate-redundancy $new $clauses)
                   (let $kept (my-car $result)
                     (let $updated (my-cdr $result)
                       (if (== $kept Nil)
                           sat  ; Saturated - no new clauses
                           (prove-loop
                             (append-lits $updated $kept)
                             (- $remaining 1)))))))))))
