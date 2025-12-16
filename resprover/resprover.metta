;;; resprover.metta - Resolution Theorem Prover
;;;
;;; Usage: ./run.sh demos/resprover.metta problem.cnf
;;;
;;; Input: DIMACS CNF file
;;; Output:
;;;   UNSAT - Shows UNSAT core (input clauses used in derivation)
;;;   SAT   - Shows variable assignments

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)

;;; Import CNF parser from Prolog FIRST
!(import_prolog_functions_from_file "demos/cnf_parser.pl"
  (parse_cnf_file))

;;; Import redundancy-based prover AFTER Prolog parser
!(import! &self resolution_prover_with_redundancy)

;;; Get command line argument (skip flags starting with --)
(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         (let $is_flag (starts-with-dash $arg)
           (if (== $is_flag True)
               (get-first-non-flag-arg (+ $idx 1))
               $arg)))))

;;; Check if string starts with --
(= (starts-with-dash $str)
   (case $str
     (("--" True)
      ($_ False))))

;;; Convert Prolog integer to MeTTa literal
(= (int-to-metta-lit $n)
   (let $metta-n (+ $n 0)  ; Force MeTTa number type
     (if (> $metta-n 0)
         (lit $metta-n)
         (nlit (- 0 $metta-n)))))

;;; Convert Prolog tuple (of integers) to MeTTa Cons list of literals
(= (tuple-to-cons $tuple)
   (if (== (size-atom $tuple) 0)
       Nil
       (let ($head $rest) (decons-atom $tuple)
         (Cons (int-to-metta-lit $head) (tuple-to-cons $rest)))))

;;; Convert nested tuples (clauses of literals) to nested Cons lists
(= (convert-clauses $tuple)
   (if (== (size-atom $tuple) 0)
       Nil
       (let ($clause $rest) (decons-atom $tuple)
         (Cons (tuple-to-cons $clause) (convert-clauses $rest)))))

;;; Convert Cons list to tuple for pretty printing
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
     (cons-atom $head $tail-list)))

;;; Check if ID is an axiom
(= (is-axiom? $id)
   (case (collapse (match &deriv (deriv $id axiom axiom) true))
     (((true) true)
      ($_ false))))

;;; Filter proof IDs to just axioms
(= (filter-axioms Nil) Nil)
(= (filter-axioms (Cons $id $rest))
   (if (== (is-axiom? $id) true)
       (Cons $id (filter-axioms $rest))
       (filter-axioms $rest)))

;;; Check if element is in list (deterministic)
(= (elem? $x Nil) false)
(= (elem? $x (Cons $head $rest))
   (if (== $x $head)
       true
       (elem? $x $rest)))

;;; Remove duplicates from list
(= (remove-dups Nil) Nil)
(= (remove-dups (Cons $x $rest))
   (if (== (elem? $x $rest) true)
       (remove-dups $rest)
       (Cons $x (remove-dups $rest))))

;;; Get clause literals by ID
(= (get-clause-lits $id)
   (match &clauses (clause-lits $id $lits) $lits))

;;; Format a single literal for display
(= (format-lit (lit $n)) $n)
(= (format-lit (nlit $n)) (- 0 $n))

;;; Format clause literals
(= (format-clause-lits Nil) ())
(= (format-clause-lits (Cons $lit $rest))
   (cons-atom (format-lit $lit) (format-clause-lits $rest)))

;;; Print each axiom clause
(= (print-axiom-clauses Nil) done)
(= (print-axiom-clauses (Cons $id $rest))
   (let $lits (get-clause-lits $id)
     (let $formatted (format-clause-lits $lits)
       (let $_ (println! (Clause $id : $formatted))
         (print-axiom-clauses $rest)))))

;;; Print derivation step with clause content
(= (print-deriv-step $id)
   (let $lits (get-clause-lits $id)
     (let $formatted (format-clause-lits $lits)
       (let $parents (car-atom (collapse (match &deriv (deriv $id $p1 $p2) ($p1 $p2))))
         (if (== $parents (axiom axiom))
             (println! ($id . $formatted [input]))
             (let $output (cons-atom resolve $parents)
               (println! ($id . $formatted $output))))))))

;;; Print derivation trace (reverse order)
(= (print-derivation Nil) done)
(= (print-derivation (Cons $id $rest))
   (let $_ (print-deriv-step $id)
     (print-derivation $rest)))

;;; Display UNSAT result with proof core
(= (display-unsat $empty-id)
   (let $all-ids (collect-proof-ids $empty-id)
     (let $axiom-ids (filter-axioms $all-ids)
       (let $unique-axioms (remove-dups $axiom-ids)
         (progn
           (println! "UNSAT")
           (println! "")
           (println! "Input clauses used (UNSAT core):")
           (print-axiom-clauses $unique-axioms)
           (println! "")
           (println! "Derivation trace:")
           (print-derivation $all-ids))))))

;;; Display SAT result
(= (display-sat)
   (println! "SAT"))

;;; Display result - use case to avoid non-determinism
(= (display-result $result)
   (case $result
     (((unsat $empty-id $steps) (display-unsat $empty-id))
      (sat (display-sat))
      ((max-iterations $n) (println! "UNKNOWN - max iterations reached"))
      ((size-limit-exceeded $n) (println! ("SIZE-LIMIT-EXCEEDED:" $n "clauses")))
      ($other (println! ("Unknown result:" $other))))))

;;; Main entry point
(= (main)
   (let $filename (get-first-non-flag-arg 0)
     (if (== $filename Empty)
         (println! "Usage: ./run.sh demos/resprover.metta problem.cnf")
         (let $prolog-clauses (collapse (parse_cnf_file $filename))
           (let $clauses (convert-clauses (car-atom $prolog-clauses))
             (let $result (car-atom (collapse (prove-once $clauses 100)))
               (display-result $result)))))))

;;; Run main
!(println! "Resolution Prover with Redundancy Elimination")
!(main)