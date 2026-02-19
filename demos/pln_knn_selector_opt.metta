;;; pln_knn_selector_opt.metta - Optimized PLN-native kNN + NB selector
;;;
;;; BATCHED PeTTa invocation. ALL reasoning in PeTTa:
;;;
;;;   kNN path:
;;;     1. Feature overlap computed by Prolog (= PeTTa's atomspace backend)
;;;        via goal_feat_db ∩ nbr_feat_db intersection, cached once per job
;;;     2. similarity = evidence-toSTV(evidence(shared, diff), kappa_sim)
;;;     3. Usage weighted by similarity → evidence per neighbor
;;;     4. evidence-hplus across neighbors (PLN Revision)
;;;
;;;   NB path:
;;;     5. IDF-weighted Naive Bayes via evidence-power + evidence-tensor
;;;        (same as pln_idf_nb_selector.metta)
;;;
;;;   Merge:
;;;     6. pln-revision(kNN_stv, NB_stv) — PLN Revision
;;;
;;; Input: ONE jobs TSV with rows:
;;;   job<TAB>job_id<TAB>data.tsv<TAB>queries.tsv
;;; Output: (Result <job_id> <qid> <axiom> (stv <strength> <confidence>))

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)
!(import! &self ../pln_inference/pln_evidence)
!(import! &self ../pln_inference/pln_rules)

!(import_prolog_function consult)

(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

!(import_prolog_functions_from_file_nocheck "demos/pln_knn_io_opt.pl"
  (load_combined_db
   load_nb_from_pl
   get_axiom_neighbor_evidence
   lookup_prior_db lookup_feature_idf_db lookup_param_db
   parse_combined_queries_file parse_jobs_file get_cmdline_arg))

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
;;; Parameter lookup with defaults
;;; --------------------------------------------------------------------------

(= (get-param $name $default)
   (let $m (lookup_param_db $name)
     (if (== $m ()) $default $m)))

(= (get-kappa)        (get-param kappa 10.0))
(= (get-global-weight) (get-param global_weight 1.0))
(= (get-sim-kappa)    (get-param sim_kappa 5.0))
(= (get-neg-weight)   (get-param neg_weight 0.5))
(= (get-used-confidence) (get-param used_confidence 0.95))
(= (get-nb-global-weight)   (get-param nb_global_weight 1.0))
(= (get-nb-confidence-kappa) (get-param nb_confidence_kappa 1000.0))

;;; ==========================================================================
;;; kNN PATH — feature overlap computed by Prolog atomspace backend
;;; ==========================================================================

;;; Per-neighbor evidence using PLN modus ponens:
;;;   sim_stv(shared,diff) and usage_stv(used) -> deduced_stv
;;; Then convert deduced STV back to evidence and downweight negatives.
(= (usage-stv $used)
   (if (> $used 0.5)
       (stv 1 (get-used-confidence))
       (stv 0 (get-used-confidence))))

(= (neighbor-evidence $shared $diff $used $sim_kappa $neg_weight)
   (let* (($sim_stv (evidence-toSTV (evidence $shared $diff) $sim_kappa))
          ($use_stv (usage-stv $used))
          ($deduced_stv (pln-modus-ponens $sim_stv $use_stv))
          ($ev0 (evidence-ofSTV $deduced_stv 1.0)))
     (if (> $used 0.5)
         $ev0
         (evidence-power $ev0 $neg_weight))))

;;; Fold neighbor rows via foldl-atom + evidence-hplus (PLN Revision)
(= (fold-nbr-evidence $rows $sk $nw)
   (foldl-atom $rows (evidence-zero) $acc $row
     (let ($nbr $shared $diff $used) $row
       (evidence-hplus $acc (neighbor-evidence $shared $diff $used $sk $nw)))))

;;; kNN score: Prolog computes overlap, MeTTa does PLN reasoning
(= (knn-score $axiom)
   (let* (($rows (get_axiom_neighbor_evidence $axiom))
          ($kappa (get-kappa))
          ($gw (get-global-weight))
          ($sk (get-sim-kappa))
          ($nw (get-neg-weight)))
     (if (== $rows ())
         (stv 0.5 0.0)
         (let* (($agg_ev (fold-nbr-evidence $rows $sk $nw))
                ($dampened (evidence-power $agg_ev $gw))
                ($stv (evidence-toSTV $dampened $kappa)))
           $stv))))

;;; ==========================================================================
;;; NB PATH — IDF-weighted Naive Bayes (from pln_idf_nb_selector.metta)
;;; ==========================================================================

(= (ln $x) (log-math 2.718281828459045 $x))
(= (safe-ln $x) (if (<= $x 0) -690.0 (ln $x)))

(= (sigmoid-diff $d)
   (if (>= $d 0)
       (/ 1 (+ 1 (exp (- 0 $d))))
       (let $z (exp $d) (/ $z (+ 1 $z)))))

(= (logsumexp2 $a $b)
   (if (>= $a $b)
       (+ $a (ln (+ 1 (exp (- $b $a)))))
       (+ $b (ln (+ 1 (exp (- $a $b)))))))

(= (get-prior-evidence $axiom)
   (let $m (lookup_prior_db $axiom)
     (if (== $m ())
         (evidence 1 1)
         (let ($p $n) $m (evidence $p $n)))))

(= (get-feature-evidence-idf $axiom $feature)
   (let $m (lookup_feature_idf_db $axiom $feature)
     (if (== $m ())
         ((evidence 1 1) 1.0)
         (let ($p $n $w) $m ((evidence $p $n) $w)))))

;;; Log-domain NB fold over features
(= (idf-nb-log-fold $axiom $features ($logPos $logNeg))
   (if (== (size-atom $features) 0)
       ($logPos $logNeg)
       (let ($f $rest) (decons-atom $features)
         (let* ((($raw_ev $w) (get-feature-evidence-idf $axiom $f))
                ((evidence $p $n) $raw_ev)
                ($newLogPos (+ $logPos (* $w (safe-ln $p))))
                ($newLogNeg (+ $logNeg (* $w (safe-ln $n)))))
           (idf-nb-log-fold $axiom $rest ($newLogPos $newLogNeg))))))

;;; NB score for one axiom
(= (nb-score $axiom $features)
   (if (== (size-atom $features) 0)
       (stv 0.5 0.0)
       (let* (($prior (get-prior-evidence $axiom))
              ((evidence $pp $pn) $prior)
              ($initLogs ((safe-ln $pp) (safe-ln $pn)))
              (($rawLogPos $rawLogNeg) (idf-nb-log-fold $axiom $features $initLogs))
              ($gwRaw (get-nb-global-weight))
              ($numFeatures (max 1 (size-atom $features)))
              ($gw (/ $gwRaw $numFeatures))
              ($logPos (* $gw $rawLogPos))
              ($logNeg (* $gw $rawLogNeg))
              ($strength (sigmoid-diff (- $logPos $logNeg)))
              ($logTotal (logsumexp2 $logPos $logNeg))
              ($kappa (get-nb-confidence-kappa))
              ($logKappa (safe-ln $kappa))
              ($conf (sigmoid-diff (- $logTotal $logKappa))))
         (stv $strength $conf))))

;;; ==========================================================================
;;; COMBINED SCORE: kNN + NB merged via PLN Revision
;;; ==========================================================================

(= (combined-score $axiom $features)
   (let* (($knn_stv (knn-score $axiom))
          ($nb_stv (nb-score $axiom $features)))
     (if (== (stv-confidence $nb_stv) 0.0)
         $knn_stv
         (if (== (stv-confidence $knn_stv) 0.0)
             $nb_stv
             (pln-revision $knn_stv $nb_stv)))))

;;; ==========================================================================
;;; Query execution — process and print one at a time
;;; ==========================================================================

(= (process-queries $jobId $qrows)
   (if (== (size-atom $qrows) 0)
       done
       (let ($q $rest) (decons-atom $qrows)
         (let ($qid $axiom $features) $q
           (let* (($stv (once (combined-score $axiom $features)))
                  ($_ (println! (Result $jobId $qid $axiom $stv))))
             (process-queries $jobId $rest))))))

(= (process-job $jobRow)
   (let ($jobId $dataFile $queryFile) $jobRow
     (let* (($_ (load_combined_db $dataFile))
            ($nbFile (lookup_param_db nb_pl_file))
            ($_nb (if (== $nbFile ()) done (load_nb_from_pl $nbFile)))
            ($queryRows (parse_combined_queries_file $queryFile)))
       (process-queries $jobId $queryRows))))

(= (process-jobs $jobs)
   (if (== (size-atom $jobs) 0)
       done
       (let ($job $rest) (decons-atom $jobs)
         (let* (($res (once (process-job $job))))
           (process-jobs $rest)))))

;;; ==========================================================================
;;; Main
;;; ==========================================================================

(= (main)
   (let $jobsFile (get-first-non-flag-arg 0)
     (if (== $jobsFile Empty)
         (println! "Usage: ./run.sh demos/pln_knn_selector_opt.metta <jobs.tsv>")
         (let* (($jobs (parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
