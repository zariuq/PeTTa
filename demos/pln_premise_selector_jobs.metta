;;; pln_premise_selector_jobs.metta - Batched PLN rule premise selector
;;;
;;; Usage:
;;;   ./run.sh demos/pln_premise_selector_jobs.metta <jobs.tsv>
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
  (load_nb_evidence_db lookup_prior_db lookup_feature_db parse_nb_queries_file get_cmdline_arg))

!(import_prolog_functions_from_file_nocheck "lib/lib_zar.pl"
  (zar_jobs_parse_jobs_file))

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

(= (derive-feature-tv $rows $axiom $feature $featureStrength)
   (let* ((($fp $fn) (get-feature-counts $rows $axiom $feature))
          ($ruleTV (nuPLN.fromEvidence $fp $fn))
          ($obsTV (stv $featureStrength 0.99)))
     (nuPLN.ModusPonens $obsTV $ruleTV)))

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

(= (default-strengths $features)
   (if (== (size-atom $features) 0)
       ()
       (let ($_ $rest) (decons-atom $features)
         (TupleConcat (1.0) (default-strengths $rest)))))

(= (query-score $rows ($qid $axiom $features))
   (let $strengths (default-strengths $features)
     (once (rule-score $rows $axiom $features $strengths))))

(= (query-score $rows ($qid $axiom $features $strengths))
   (once (rule-score $rows $axiom $features $strengths)))

(= (process-one-query $jobId $rows ($qid $axiom $features))
   (let* (($stv (query-score $rows ($qid $axiom $features)))
          ($_ (println! (Result $jobId $qid $axiom $stv))))
     done))

(= (process-one-query $jobId $rows ($qid $axiom $features $strengths))
   (let* (($stv (query-score $rows ($qid $axiom $features $strengths)))
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
         (println! "Usage: ./run.sh demos/pln_premise_selector_jobs.metta <jobs.tsv>")
         (let* (($jobs (zar_jobs_parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
