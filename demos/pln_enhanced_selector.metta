;;; pln_enhanced_selector.metta - Two-phase PLN selector with co-occurrence revision
;;;
;;; Uses PLN rules from the verified library:
;;;   - pln-modus-ponens: partner_useful ∧ (partner co-occurs with target) ⊢ target_useful
;;;   - evidence-power: IDF regraduation (Knuth-Skilling) on per-partner evidence
;;;   - evidence-hplus: revision (independent evidence pooling) across partners
;;;   - evidence-toSTV: convert aggregate evidence to STV with κ-controlled confidence
;;;   - pln-revision (Truth_Revision): final combination of phase-1 + co-occurrence boost
;;;
;;; Architecture:
;;;   Phase 1 (external): IDF-NB produces initial STVs
;;;   Phase 2 (this script):
;;;     For each target axiom φ:
;;;       1. For each co-occurring partner ψ:
;;;          a. pln-modus-ponens(phase1(ψ), cooc(ψ→φ)) → deduced STV
;;;          b. evidence-ofSTV(deduced) → evidence counts
;;;          c. evidence-power(evidence, cooc_idf(ψ)) → IDF-weighted evidence
;;;       2. evidence-hplus all partner evidence (= PLN Revision of independent sources)
;;;       3. evidence-power(combined, global_weight) → dampened evidence
;;;       4. evidence-toSTV(dampened, κ) → boost STV with bounded confidence
;;;       5. pln-revision(phase1_stv, boost_stv) → final STV
;;;
;;; Key insight: κ controls the maximum influence of co-occurrence.
;;;   κ = 10 → boost confidence ≤ ~0.17 → ~8% weight in final revision
;;;   κ = 20 → boost confidence ≤ ~0.09 → ~4% weight
;;;   κ = 5  → boost confidence ≤ ~0.29 → ~14% weight
;;;
;;; Input format (TSV):
;;;   init<TAB>axiom<TAB>strength<TAB>confidence          (phase 1 STVs)
;;;   cooc<TAB>axiom_A<TAB>axiom_B<TAB>pos<TAB>neg<TAB>idf (co-occurrence + IDF)
;;;   param<TAB>global_weight<TAB>value                    (co-occurrence dampening)
;;;   param<TAB>kappa<TAB>value                            (evidence prior weight)
;;;   query<TAB>query_id<TAB>axiom                         (which axioms to score)
;;;
;;; Output:
;;;   (Result <query_id> <axiom> (stv <strength> <confidence>))

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln_nu)
!(import! &self ../pln_inference/pln_evidence)
!(import! &self ../pln_inference/pln_rules)

!(import_prolog_function consult)

(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

!(import_prolog_functions_from_file_nocheck "demos/pln_enhanced_io.pl"
  (load_enhanced_db lookup_init_stv_db lookup_cooc_partners_idf_db
   lookup_param_db parse_enhanced_queries_file get_cmdline_arg))

;;; --------------------------------------------------------------------------
;;; CLI helpers
;;; --------------------------------------------------------------------------

(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         (if (== $arg "--")
             (get-first-non-flag-arg (+ $idx 1))
             $arg))))

;;; --------------------------------------------------------------------------
;;; Phase 1 score lookup
;;; --------------------------------------------------------------------------

(= (get-init-stv $axiom)
   (let $m (lookup_init_stv_db $axiom)
     (if (== $m ())
         (stv 0.5 0.01)
         (let ($s $c) $m
           (stv $s $c)))))

;;; --------------------------------------------------------------------------
;;; Parameter lookup with defaults
;;; --------------------------------------------------------------------------

(= (get-global-weight)
   (let $m (lookup_param_db global_weight)
     (if (== $m ())
         0.05
         $m)))

(= (get-kappa)
   (let $m (lookup_param_db kappa)
     (if (== $m ())
         10.0
         $m)))

;;; --------------------------------------------------------------------------
;;; Per-partner evidence via PLN Modus Ponens + IDF weighting
;;;
;;; For partner ψ co-occurring with target φ:
;;;   1. pln-modus-ponens(phase1(ψ), cooc_stv(ψ→φ)) → deduced STV
;;;   2. evidence-ofSTV(deduced) → evidence counts
;;;   3. evidence-power(evidence, idf) → IDF-weighted (rare partners count more)
;;; --------------------------------------------------------------------------

(= (partner-evidence $partner $cooc_pos $cooc_neg $cooc_idf)
   (let* (($partner_stv (get-init-stv $partner))
          ($cooc_stv (evidence-to-stv $cooc_pos $cooc_neg))
          ($deduced_stv (pln-modus-ponens $partner_stv $cooc_stv))
          ($deduced_ev (evidence-ofSTV $deduced_stv))
          ($weighted_ev (evidence-power $deduced_ev $cooc_idf)))
     $weighted_ev))

;;; --------------------------------------------------------------------------
;;; Fold partners: accumulate evidence via evidence-hplus (= PLN Revision)
;;;
;;; Independent partner observations combine additively (hplus),
;;; NOT multiplicatively (tensor, which is for sequential chains).
;;; --------------------------------------------------------------------------

(= (fold-partners-hplus $partners $acc)
   (if (== (size-atom $partners) 0)
       $acc
       (let ($entry $rest) (decons-atom $partners)
         (let ($partner $pos $neg $idf) $entry
           (let $contrib (partner-evidence $partner $pos $neg $idf)
             (fold-partners-hplus $rest (evidence-hplus $acc $contrib)))))))

;;; --------------------------------------------------------------------------
;;; Enhanced score: phase-1 revised with κ-bounded co-occurrence boost
;;;
;;; Steps:
;;;   1. Accumulate partner evidence via hplus (independent revision)
;;;   2. Global dampening via evidence-power → small evidence counts
;;;   3. Convert to STV with κ → bounded confidence
;;;   4. PLN Revision with phase-1 → weighted average (phase-1 dominates)
;;; --------------------------------------------------------------------------

(= (enhanced-score $axiom)
   (let* (($init_stv (get-init-stv $axiom))
          ($partners (lookup_cooc_partners_idf_db $axiom)))
     (if (== $partners ())
         ;; No co-occurrence data: return phase-1 STV as-is
         $init_stv
         ;; Has partners: compute bounded co-occurrence boost
         (let* (;; 1. Combine all partner evidence via revision (hplus)
                ($combined_ev (fold-partners-hplus $partners (evidence-zero)))
                ;; 2. Global dampening: shrink co-occurrence evidence
                ($gw (get-global-weight))
                ($dampened_ev (evidence-power $combined_ev $gw))
                ;; 3. Convert to STV with large κ → low confidence
                ($kappa (get-kappa))
                ($boost_stv (evidence-toSTV $dampened_ev $kappa))
                ;; 4. PLN Revision: weighted average, phase-1 dominates
                ($result (pln-revision $init_stv $boost_stv)))
           $result))))

;;; --------------------------------------------------------------------------
;;; Query execution
;;; --------------------------------------------------------------------------

(= (score-one-query $rows ($qid $axiom))
   (Result $qid $axiom (once (enhanced-score $axiom))))

(= (score-all-queries $rows $qrows)
   (if (== (size-atom $qrows) 0)
       ()
       (let ($q $rest) (decons-atom $qrows)
         (cons-atom
           (score-one-query $rows $q)
           (score-all-queries $rows $rest)))))

(= (print-results $rows)
   (if (== (size-atom $rows) 0)
       done
       (let ($r $rest) (decons-atom $rows)
         (let $_ (println! $r)
           (print-results $rest)))))

;;; --------------------------------------------------------------------------
;;; Main
;;; --------------------------------------------------------------------------

(= (main)
   (let $dataFile (get-first-non-flag-arg 0)
     (let $queryFile (get-first-non-flag-arg 1)
       (if (or (== $dataFile Empty) (== $queryFile Empty))
           (println! "Usage: ./run.sh demos/pln_enhanced_selector.metta <data.tsv> <queries.tsv>")
           (let* (($_ (load_enhanced_db $dataFile))
                  ($queryRows (parse_enhanced_queries_file $queryFile))
                  ($results (score-all-queries () $queryRows)))
             (print-results $results))))))

!(once (main))
