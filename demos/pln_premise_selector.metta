;;; pln_premise_selector.metta - Proper PLN-based Premise Selector
;;;
;;; INFERENCE STRATEGY:
;;;   Uses nuPLN rule functions directly:
;;;   1. Modus Ponens over feature observation + feature=>useful rule TV
;;;   2. Revision to aggregate multiple feature-derived useful TVs
;;;
;;; PLN RULES USED (from lib_pln_nu.metta):
;;;   - nuPLN.ModusPonens
;;;   - nuPLN.Revision
;;;   - nuPLN.fromEvidence
;;;
;;; DIFFERENCE FROM NAIVE BAYES:
;;;   - NB: multiplies likelihood ratios in log-odds space
;;;   - PLN: chains Modus Ponens + combines via Revision (weighted averaging)
;;;   → Different math, different semantics, same spirit (feature-based inference)
;;;
;;; Usage:
;;;   ./run.sh demos/pln_premise_selector.metta <evidence.tsv> <queries.tsv>
;;;
;;; Input format:
;;;   Evidence: prior\t<axiom>\t<pos>\t<neg>
;;;             feat\t<axiom>\t<feature>\t<pos>\t<neg>[\t<strength>]
;;;   Queries:  <query_id>\t<axiom>\t<feature1>,<feature2>,...[\t<f1_strength>,<f2_strength>,...]
;;;
;;; Output:
;;;   (Result <query_id> <axiom> (stv <strength> <confidence>))

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln_nu)

!(import_prolog_function consult)

(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

!(import_prolog_functions_from_file_nocheck "demos/pln_premise_io.pl"
  (load_nb_evidence_db lookup_prior_db lookup_feature_db parse_nb_queries_file get_cmdline_arg))

;;; --------------------------------------------------------------------------
;;; CLI helpers
;;; --------------------------------------------------------------------------

(= (starts-with-dash $str)
   (case $str
     (("--" True)
      ($_ False))))

(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         (let $is_flag (starts-with-dash $arg)
           (if (== $is_flag True)
               (get-first-non-flag-arg (+ $idx 1))
               $arg)))))

;;; --------------------------------------------------------------------------
;;; Evidence lookup
;;; --------------------------------------------------------------------------

(= (lookup-prior $rows $axiom)
   (lookup_prior_db $axiom))

(= (lookup-feature $rows $axiom $feature)
   (lookup_feature_db $axiom $feature))

(= (get-prior-counts $rows $axiom)
   (let $m (lookup-prior $rows $axiom)
     (if (== $m ())
         (1 1)
         $m)))

(= (get-feature-counts $rows $axiom $feature)
   (let $m (lookup-feature $rows $axiom $feature)
     (if (== $m ())
         (1 1)
         $m)))

;;; Derive one useful-TV contribution by Modus Ponens on:
;;;   feature observation TV + feature->useful rule TV
;;; $featureStrength: strength of feature observation (default 1.0 for binary)
;;;   For Enigma: use feature value from sparse vector
(= (derive-feature-tv $rows $axiom $feature $featureStrength)
   (let* ((($fp $fn) (get-feature-counts $rows $axiom $feature))
          ($ruleTV (nuPLN.fromEvidence $fp $fn))
          ($obsTV (stv $featureStrength 0.99)))  ; Feature observation with given strength
     (nuPLN.ModusPonens $obsTV $ruleTV)))

;;; Fold feature contributions into a single useful-TV via Revision rule.
;;; $features: list of feature names
;;; $strengths: list of feature observation strengths (parallel to $features)
(= (fold-feature-tvs $rows $axiom $features $strengths $curTV)
   (if (== (size-atom $features) 0)
       $curTV
       (let* ((($f $restF) (decons-atom $features))
              (($s $restS) (decons-atom $strengths))
              ($featTV (derive-feature-tv $rows $axiom $f $s))
              ($newTV (nuPLN.Revision $curTV $featTV)))
         (fold-feature-tvs $rows $axiom $restF $restS $newTV))))

(= (rule-score $rows $axiom $features $strengths)
   (let* ((($pp $pn) (get-prior-counts $rows $axiom))
          ($priorTV (nuPLN.fromEvidence $pp $pn)))
     (fold-feature-tvs $rows $axiom $features $strengths $priorTV)))

;;; --------------------------------------------------------------------------
;;; Query execution
;;; --------------------------------------------------------------------------

;;; Helper: create default strengths (all 1.0) for binary features
(= (default-strengths $features)
   (if (== (size-atom $features) 0)
       ()
       (let ($_ $rest) (decons-atom $features)
         (TupleConcat (1.0) (default-strengths $rest)))))

;;; Score a query with optional feature strengths
;;; Query format: ($qid $axiom $features) or ($qid $axiom $features $strengths)
(= (score-one-query $rows ($qid $axiom $features))
   (let $strengths (default-strengths $features)
     (Result $qid $axiom (rule-score $rows $axiom $features $strengths))))

(= (score-one-query $rows ($qid $axiom $features $strengths))
   (Result $qid $axiom (rule-score $rows $axiom $features $strengths)))

(= (score-all-queries $rows $qrows)
   (if (== (size-atom $qrows) 0)
       ()
       (let ($q $rest) (decons-atom $qrows)
         (TupleConcat
           ((score-one-query $rows $q))
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
   (let $evidenceFile (get-first-non-flag-arg 0)
     (let $queryFile (get-first-non-flag-arg 1)
       (if (or (== $evidenceFile Empty) (== $queryFile Empty))
           (println! "Usage: ./run.sh demos/pln_rule_nb_selector.metta <evidence.tsv> <queries.tsv>")
           (let* (($_ (load_nb_evidence_db $evidenceFile))
                  ($queryRows (parse_nb_queries_file $queryFile))
                  ($results (car-atom (collapse (score-all-queries () $queryRows)))))
             (print-results $results))))))

!(main)
