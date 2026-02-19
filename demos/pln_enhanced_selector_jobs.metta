;;; pln_enhanced_selector_jobs.metta - Batched co-occurrence revision selector
;;;
;;; Usage:
;;;   ./run.sh demos/pln_enhanced_selector_jobs.metta <jobs.tsv>
;;;
;;; Jobs TSV format:
;;;   job<TAB>job_id<TAB>data.tsv<TAB>queries.tsv
;;;
;;; Output lines:
;;;   (Result <job_id> <query_id> <axiom> (stv <strength> <confidence>))

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

!(import_prolog_functions_from_file_nocheck "lib/lib_zar.pl"
  (zar_jobs_parse_jobs_file))

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
;;; Parameter lookup
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
;;; Co-occurrence revision scoring
;;; --------------------------------------------------------------------------

(= (partner-evidence $partner $cooc_pos $cooc_neg $cooc_idf)
   (let* (($partner_stv (get-init-stv $partner))
          ($cooc_stv (evidence-to-stv $cooc_pos $cooc_neg))
          ($deduced_stv (pln-modus-ponens $partner_stv $cooc_stv))
          ($deduced_ev (evidence-ofSTV $deduced_stv))
          ($weighted_ev (evidence-power $deduced_ev $cooc_idf)))
     $weighted_ev))

(= (fold-partners-hplus $partners $acc)
   (if (== (size-atom $partners) 0)
       $acc
       (let ($entry $rest) (decons-atom $partners)
         (let ($partner $pos $neg $idf) $entry
           (let $contrib (partner-evidence $partner $pos $neg $idf)
             (fold-partners-hplus $rest (evidence-hplus $acc $contrib)))))))

(= (enhanced-score $axiom)
   (let* (($init_stv (get-init-stv $axiom))
          ($partners (lookup_cooc_partners_idf_db $axiom)))
     (if (== $partners ())
         $init_stv
         (let* (($combined_ev (fold-partners-hplus $partners (evidence-zero)))
                ($gw (get-global-weight))
                ($dampened_ev (evidence-power $combined_ev $gw))
                ($kappa (get-kappa))
                ($boost_stv (evidence-toSTV $dampened_ev $kappa))
                ($result (pln-revision $init_stv $boost_stv)))
           $result))))

;;; --------------------------------------------------------------------------
;;; Batched query execution
;;; --------------------------------------------------------------------------

(= (process-one-query $jobId ($qid $axiom))
   (let* (($stv (once (enhanced-score $axiom)))
          ($_ (println! (Result $jobId $qid $axiom $stv))))
     done))

(= (process-queries $jobId $qrows)
   (if (== (size-atom $qrows) 0)
       done
       (let ($q $rest) (decons-atom $qrows)
         (let* (($_ (process-one-query $jobId $q)))
           (process-queries $jobId $rest)))))

(= (process-job $jobRow)
   (let ($jobId $dataFile $queryFile) $jobRow
     (let* (($_ (load_enhanced_db $dataFile))
            ($queryRows (parse_enhanced_queries_file $queryFile)))
       (process-queries $jobId $queryRows))))

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
         (println! "Usage: ./run.sh demos/pln_enhanced_selector_jobs.metta <jobs.tsv>")
         (let* (($jobs (zar_jobs_parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
