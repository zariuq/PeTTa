;;; pln_knn_prior_nb_selector_opt.metta - PLN kNN-prior + NB-likelihood selector
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
;;;   Prior/Likelihood split:
;;;     5. Build global prior evidence from tfreq prior rows
;;;     6. Build kNN prior evidence from neighbor observations
;;;     7. prior_goal = hplus(global_prior, knn_prior)
;;;     8. NB likelihood from features only (no prior term)
;;;     9. posterior logs = prior_goal logs + NB likelihood logs
;;;
;;; Selector semantics ↔ theorem assumptions (Lean-side mapping):
;;;   - Finite pool / top-k surrogate:
;;;       `PriorNBAssumptionChecklist.topK`, `topK_le_pool`
;;;       (Mettapedia/Logic/PremiseSelectionPriorNB.lean)
;;;   - Role-correct composition:
;;;       prior via `fuse/hplus`, likelihood via `update/tensor`
;;;       (Mettapedia/Logic/PremiseSelectionOperatorRoles.lean)
;;;   - Prior-NB commutation:
;;;       `priorNBPosterior_eq_twoStage`
;;;       (Mettapedia/Logic/PremiseSelectionPriorNB.lean)
;;;   - Finite local-mixture approximation (m=16, R=4551):
;;;       TV ≤ 120/4551
;;;       (Mettapedia/Logic/PremiseSelectionLocalMixtureBridge.lean)
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
(= (get-neg-weight)   (get-param neg_weight 0.05))
(= (get-tau-power)    (get-param tau_power 6.0))
(= (get-deps-factor)  (get-param deps_factor 2.7))
(= (get-gate-kappa)   (get-param gate_kappa 10.0))
(= (get-used-confidence) (get-param used_confidence 0.95))
(= (get-nb-global-weight)   (get-param nb_global_weight 1.0))
(= (get-nb-confidence-kappa) (get-param nb_confidence_kappa 1000.0))
(= (get-post-confidence-kappa) (get-param post_confidence_kappa (get-nb-confidence-kappa)))

;;; ==========================================================================
;;; kNN PATH — feature overlap computed by Prolog atomspace backend
;;; ==========================================================================

;;; Per-neighbor evidence using PLN modus ponens:
;;;   sim_stv(shared,diff) and usage_stv(used) -> deduced_stv
;;; Tau/deps are applied via evidence-power regraduation.
(= (usage-stv $used)
   (if (> $used 0.5)
       (stv 1 (get-used-confidence))
       (stv 0 (get-used-confidence))))

;;; Tau regraduation on similarity evidence, then convert to STV for MP.
(= (regraded-sim-stv $shared $diff $sim_kappa $tau_power)
   (let* (($sim0 (evidence-toSTV (evidence $shared $diff) $sim_kappa))
          ($simEv0 (evidence-ofSTV $sim0 1.0))
          ($simEvTau (evidence-power $simEv0 $tau_power)))
     (evidence-toSTV $simEvTau 1.0)))

;;; Returns pair: (rowEvidence simMass)
(= (neighbor-row-inference $shared $diff $used $sim_kappa $tau_power $neg_weight $deps_factor)
   (let* (($sim_stv (regraded-sim-stv $shared $diff $sim_kappa $tau_power))
          ($sim_s (stv-strength $sim_stv))
          ($use_stv (usage-stv $used))
          ($deduced_stv (pln-modus-ponens $sim_stv $use_stv))
          ($ev0 (evidence-ofSTV $deduced_stv 1.0))
          ($ev1 (if (> $used 0.5)
                    (evidence-power $ev0 $deps_factor)
                    (evidence-power $ev0 $neg_weight))))
     ($ev1 $sim_s)))

;;; Fold neighbor rows via foldl-atom + evidence-hplus (PLN Revision),
;;; while tracking neighborhood mass for reliability gating.
(= (fold-nbr-evidence-mass $rows $sk $tau $nw $df)
   (foldl-atom $rows ((evidence-zero) 0.0) $acc $row
     (let* ((($evAcc $massAcc) $acc)
            (($nbr $shared $diff $used) $row)
            (($evRow $simMass) (neighbor-row-inference $shared $diff $used $sk $tau $nw $df)))
       ((evidence-hplus $evAcc $evRow) (+ $massAcc $simMass)))))

(= (gate-from-mass $mass $kg)
   (if (<= $mass 0.0)
       0.0
       (/ $mass (+ $mass (max 0.000000001 $kg)))))

;;; kNN prior evidence: Prolog computes overlap, MeTTa does PLN reasoning
(= (knn-prior-evidence $axiom)
   (let* (($rows (get_axiom_neighbor_evidence $axiom))
          ($gw (get-global-weight))
          ($sk (get-sim-kappa))
          ($nw (get-neg-weight))
          ($tau (get-tau-power))
          ($df (get-deps-factor))
          ($kg (get-gate-kappa)))
     (if (== $rows ())
         (evidence-zero)
         (let* ((($agg_ev $mass) (fold-nbr-evidence-mass $rows $sk $tau $nw $df))
                ($gate (gate-from-mass $mass $kg))
                ($gated (evidence-power $agg_ev $gate))
                ($dampened (evidence-power $gated $gw)))
           $dampened))))

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

;;; Log-domain NB likelihood fold over features (no prior term included)
(= (idf-nb-likelihood-log-fold $axiom $features ($logPos $logNeg))
   (if (== (size-atom $features) 0)
       ($logPos $logNeg)
       (let ($f $rest) (decons-atom $features)
         (let* ((($raw_ev $w) (get-feature-evidence-idf $axiom $f))
                ((evidence $p $n) $raw_ev)
                ($newLogPos (+ $logPos (* $w (safe-ln $p))))
                ($newLogNeg (+ $logNeg (* $w (safe-ln $n)))))
           (idf-nb-likelihood-log-fold $axiom $rest ($newLogPos $newLogNeg))))))

;;; NB likelihood logs for one axiom
(= (nb-likelihood-logs $axiom $features)
   (let* (($gwRaw (get-nb-global-weight))
          ($numFeatures (max 1 (size-atom $features)))
          ($gw (/ $gwRaw $numFeatures))
          (($rawLogPos $rawLogNeg) (idf-nb-likelihood-log-fold $axiom $features (0.0 0.0)))
          ($logPos (* $gw $rawLogPos))
          ($logNeg (* $gw $rawLogNeg)))
     ($logPos $logNeg)))

;;; Prior evidence: global tfreq prior revised with kNN prior evidence
(= (prior-goal-evidence $axiom)
   (let* (($global (get-prior-evidence $axiom))
          ($knn (knn-prior-evidence $axiom)))
     (evidence-hplus $global $knn)))

;;; Final score from prior + likelihood composition in log-domain
(= (prior-likelihood-score $axiom $features)
   (let* (($priorEv (prior-goal-evidence $axiom))
          ((evidence $pp $pn) $priorEv)
          ($priorLogPos (safe-ln $pp))
          ($priorLogNeg (safe-ln $pn)))
     (if (== (size-atom $features) 0)
         (evidence-toSTV $priorEv (get-kappa))
         (let* ((($likeLogPos $likeLogNeg) (nb-likelihood-logs $axiom $features))
                ($logPos (+ $priorLogPos $likeLogPos))
                ($logNeg (+ $priorLogNeg $likeLogNeg))
                ($strength (sigmoid-diff (- $logPos $logNeg)))
                ($logTotal (logsumexp2 $logPos $logNeg))
                ($kappa (get-post-confidence-kappa))
                ($logKappa (safe-ln $kappa))
                ($conf (sigmoid-diff (- $logTotal $logKappa))))
           (stv $strength $conf)))))

;;; ==========================================================================
;;; COMBINED SCORE: kNN-prior + NB-likelihood
;;; ==========================================================================

(= (combined-score $axiom $features)
   (prior-likelihood-score $axiom $features))

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
         (println! "Usage: ./run.sh demos/pln_knn_prior_nb_selector_opt.metta <jobs.tsv>")
         (let* (($jobs (parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
