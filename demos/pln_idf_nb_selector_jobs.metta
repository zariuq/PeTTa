;;; pln_idf_nb_selector_jobs.metta - Batched IDF-weighted PLN Naive Bayes selector
;;;
;;; Usage:
;;;   ./run.sh demos/pln_idf_nb_selector_jobs.metta <jobs.tsv>
;;;
;;; Jobs TSV format:
;;;   job<TAB>job_id<TAB>evidence.tsv<TAB>queries.tsv
;;;
;;; Output lines:
;;;   (Result <job_id> <query_id> <axiom> (stv <strength> <confidence>))

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

!(import_prolog_functions_from_file_nocheck "lib/lib_zar.pl"
  (zar_jobs_parse_jobs_file
   zar_math_safe_ln
   zar_math_sigmoid_diff
   zar_math_logsumexp2))

;;; --------------------------------------------------------------------------
;;; Evidence lookup
;;; --------------------------------------------------------------------------

(= (lookup-prior $rows $axiom)
   (lookup_prior_db $axiom))

(= (lookup-feature-idf $rows $axiom $feature)
   (lookup_feature_idf_db $axiom $feature))

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
;;; Stable log-domain NB scoring
;;; --------------------------------------------------------------------------

(= (sigmoid-shift $logTotal $logKappa)
   (zar_math_sigmoid_diff (- $logTotal $logKappa)))

(= (idf-nb-log-fold $rows $axiom $features ($logPos $logNeg))
   (if (== (size-atom $features) 0)
       ($logPos $logNeg)
         (let ($f $rest) (decons-atom $features)
         (let* ((($raw_ev $w) (get-feature-evidence-idf $rows $axiom $f))
                ((evidence $p $n) $raw_ev)
                ($newLogPos (+ $logPos (* $w (zar_math_safe_ln $p))))
                ($newLogNeg (+ $logNeg (* $w (zar_math_safe_ln $n)))))
           (idf-nb-log-fold $rows $axiom $rest ($newLogPos $newLogNeg))))))

(= (idf-nb-score $rows $axiom $features)
   (let* (($prior (get-prior-evidence $rows $axiom))
          ((evidence $pp $pn) $prior)
          ($initLogs ((zar_math_safe_ln $pp) (zar_math_safe_ln $pn)))
          (($rawLogPos $rawLogNeg) (idf-nb-log-fold $rows $axiom $features $initLogs))
          ($gwRaw (get-global-weight))
          ($numFeatures (max 1 (size-atom $features)))
          ($gw (/ $gwRaw $numFeatures))
          ($logPos (* $gw $rawLogPos))
          ($logNeg (* $gw $rawLogNeg))
          ($strength (zar_math_sigmoid_diff (- $logPos $logNeg)))
          ($logTotal (zar_math_logsumexp2 $logPos $logNeg))
          ($kappa (get-confidence-kappa))
          ($logKappa (zar_math_safe_ln $kappa))
          ($conf (sigmoid-shift $logTotal $logKappa)))
     (stv $strength $conf)))

;;; --------------------------------------------------------------------------
;;; Batched query execution
;;; --------------------------------------------------------------------------

(= (process-one-query $jobId $rows ($qid $axiom $features))
   (let* (($stv (once (idf-nb-score $rows $axiom $features)))
          ($_ (println! (Result $jobId $qid $axiom $stv))))
     done))

(= (process-queries $jobId $rows $qrows)
   (if (== (size-atom $qrows) 0)
       done
       (let ($q $rest) (decons-atom $qrows)
         (let* (($_ (process-one-query $jobId $rows $q)))
           (process-queries $jobId $rows $rest)))))

(= (process-job $jobRow)
   (let ($jobId $evidenceFile $queryFile) $jobRow
     (let* (($_ (load_nb_evidence_db $evidenceFile))
            ($queryRows (parse_nb_queries_file $queryFile)))
       (process-queries $jobId () $queryRows))))

(= (process-jobs $jobs)
   (if (== (size-atom $jobs) 0)
       done
       (let ($job $rest) (decons-atom $jobs)
         (let* (($res (once (process-job $job))))
           (process-jobs $rest)))))

;;; --------------------------------------------------------------------------
;;; Main
;;; --------------------------------------------------------------------------

(= (main)
   (let $jobsFile (once (get_cmdline_arg 0))
     (if (== $jobsFile Empty)
         (println! "Usage: ./run.sh demos/pln_idf_nb_selector_jobs.metta <jobs.tsv>")
         (let* (($jobs (zar_jobs_parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
