;;; pln_idf_nb_selector.metta - IDF-weighted PLN Naive Bayes premise selector
;;;
;;; MATHEMATICAL FOUNDATION (provably correct, for later Lean formalization):
;;;
;;;   The IDF weight w(f) acts as a REGRADUATION parameter on evidence:
;;;     power(Evidence(p, n), w) = Evidence(p^w, n^w)
;;;
;;;   Key theorem (log-odds linearity):
;;;     logOdds(power(e, w)) = w * logOdds(e)
;;;
;;;   Therefore, the IDF-weighted NB posterior decomposes as:
;;;     logOdds(prior ⊗ ∏_f power(likelihood_f, w_f))
;;;       = logOdds(prior) + Σ_f w_f * logOdds(likelihood_f)
;;;
;;;   This is exactly weighted Naive Bayes in log-odds space.
;;;   The power-scaling is a Σ-guarded operation (WM calculus, Section 6):
;;;     Σ = "features are informativeness-weighted by IDF"
;;;
;;; PLN RULES USED:
;;;   - evidence-tensor: sequential composition (independence assumption)
;;;   - evidence-power: regraduation by informativeness weight
;;;   - evidence-toStrength: view projection (evidence → probability)
;;;
;;; Usage:
;;;   ./run.sh demos/pln_idf_nb_selector.metta <evidence.tsv> <queries.tsv>
;;;
;;; Evidence TSV format (with IDF column):
;;;   param<TAB>global_weight<TAB>value
;;;   param<TAB>confidence_kappa<TAB>value
;;;   prior<TAB>axiom<TAB>pos<TAB>neg
;;;   feat<TAB>axiom<TAB>feature<TAB>pos<TAB>neg<TAB>idf_weight

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln_nu)

!(import_prolog_function consult)

(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

!(import_prolog_functions_from_file_nocheck "demos/pln_premise_io.pl"
  (load_nb_evidence_db lookup_prior_db lookup_feature_idf_db lookup_param_db
   parse_nb_queries_file get_cmdline_arg))

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
;;; Evidence lookup (extended for IDF weight column)
;;; --------------------------------------------------------------------------

(= (lookup-prior $rows $axiom)
   (lookup_prior_db $axiom))

;;; Feature rows now have 6 elements: (feat axiom feature pos neg idf)
(= (lookup-feature-idf $rows $axiom $feature)
   (lookup_feature_idf_db $axiom $feature))

;;; Optional calibration params from evidence TSV.
;;; global_weight: evidence regraduation exponent for the whole posterior.
;;; confidence_kappa: confidence scale c = total/(total+kappa).
(= (get-global-weight)
   (let $m (lookup_param_db global_weight)
     (if (== $m ())
         1.0
         $m)))

(= (get-confidence-kappa)
   (let $m (lookup_param_db confidence_kappa)
     (if (== $m ())
         1.0
         (max 0.0000001 $m))))

(= (get-prior-evidence $rows $axiom)
   (let $m (lookup-prior $rows $axiom)
     (if (== $m ())
         (evidence 1 1)
         (let ($p $n) $m
           (evidence $p $n)))))

(= (get-feature-evidence-idf $rows $axiom $feature)
   (let $m (lookup-feature-idf $rows $axiom $feature)
     (if (== $m ())
         ((evidence 1 1) 1.0)
         (let ($p $n $w) $m
           ((evidence $p $n) $w)))))

;;; --------------------------------------------------------------------------
;;; IDF-weighted NB scoring via evidence power-scaling
;;;
;;; posterior = prior ⊗ ∏_f power(likelihood_f, w_f)
;;;
;;; Provability note:
;;;   evidence-power commutes with evidence-tensor in log-odds space:
;;;     logOdds(power(e,w)) = w * logOdds(e)
;;;   This is the regraduation theorem (Knuth-Skilling §6).
;;; --------------------------------------------------------------------------

;;; Use numerically stable log-domain accumulation.
;;; This is exactly equivalent to tensor/power scoring by the log-odds theorem.

(= (ln $x) (log-math 2.718281828459045 $x))

(= (safe-ln $x)
   (if (<= $x 0)
       -690.0
       (ln $x)))

(= (logsumexp2 $a $b)
   (if (>= $a $b)
       (+ $a (ln (+ 1 (exp (- $b $a)))))
       (+ $b (ln (+ 1 (exp (- $a $b)))))))

(= (sigmoid-diff $d)
   (if (>= $d 0)
       (/ 1 (+ 1 (exp (- 0 $d))))
       (let $z (exp $d)
         (/ $z (+ 1 $z)))))

;;; Stable sigmoid(logTotal - logKappa) for c = total/(total+kappa).
(= (sigmoid-shift $logTotal $logKappa)
   (sigmoid-diff (- $logTotal $logKappa)))

(= (idf-nb-log-fold $rows $axiom $features ($logPos $logNeg))
   (if (== (size-atom $features) 0)
       ($logPos $logNeg)
       (let ($f $rest) (decons-atom $features)
         (let* ((($raw_ev $w) (get-feature-evidence-idf $rows $axiom $f))
                ((evidence $p $n) $raw_ev)
                ($newLogPos (+ $logPos (* $w (safe-ln $p))))
                ($newLogNeg (+ $logNeg (* $w (safe-ln $n)))))
           (idf-nb-log-fold $rows $axiom $rest ($newLogPos $newLogNeg))))))

(= (idf-nb-score $rows $axiom $features)
   (let* (($prior (get-prior-evidence $rows $axiom))
          ((evidence $pp $pn) $prior)
          ($initLogs ((safe-ln $pp) (safe-ln $pn)))
          (($rawLogPos $rawLogNeg) (idf-nb-log-fold $rows $axiom $features $initLogs))
          ;; Global PLN-aligned regraduation budget normalized by feature count.
          ;; This keeps total evidence growth controlled as feature count increases.
          ($gwRaw (get-global-weight))
          ($numFeatures (max 1 (size-atom $features)))
          ($gw (/ $gwRaw $numFeatures))
          ($logPos (* $gw $rawLogPos))
          ($logNeg (* $gw $rawLogNeg))
          ($strength (sigmoid-diff (- $logPos $logNeg)))
          ($logTotal (logsumexp2 $logPos $logNeg))
          ($kappa (get-confidence-kappa))
          ($logKappa (safe-ln $kappa))
          ($conf (sigmoid-shift $logTotal $logKappa))
          )
     (stv $strength $conf)))

;;; --------------------------------------------------------------------------
;;; Query execution
;;; --------------------------------------------------------------------------

(= (score-one-query $rows ($qid $axiom $features))
   (Result $qid $axiom (once (idf-nb-score $rows $axiom $features))))

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
           (println! "Usage: ./run.sh demos/pln_idf_nb_selector.metta <evidence.tsv> <queries.tsv>")
           (let* (($_ (load_nb_evidence_db $evidenceFile))
                  ($queryRows (parse_nb_queries_file $queryFile))
                  ($results (score-all-queries () $queryRows)))
             (print-results $results))))))

!(once (main))
