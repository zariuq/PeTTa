;;; pln_normal_nb_selector_jobs.metta - Batched Normal-Normal PLN selector
;;;
;;; Usage:
;;;   ./run.sh demos/pln_normal_nb_selector_jobs.metta <jobs.tsv>
;;;
;;; Jobs TSV format:
;;;   job<TAB>job_id<TAB>data.tsv<TAB>queries.tsv
;;;
;;; Output lines:
;;;   (Result <job_id> <query_id> <axiom> (stv <strength> <confidence>))

!(import! &self ../lib/lib_import)
!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln_xi)

!(import_prolog_function consult)

(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

!(import_prolog_functions_from_file_nocheck "demos/pln_normal_io.pl"
  (load_normal_db lookup_normal_obs_db lookup_normal_param_db
   parse_normal_queries_file get_cmdline_arg))

!(import_prolog_functions_from_file_nocheck "lib/lib_zar.pl"
  (zar_jobs_parse_jobs_file))

;;; --------------------------------------------------------------------------
;;; Params
;;; --------------------------------------------------------------------------

(= (get-param $name $default)
   (let $m (lookup_normal_param_db $name)
     (if (== $m ())
         $default
         $m)))

(= (get-mu0) (get-param mu0 0.0))
(= (get-tau0-sq) (max 0.000001 (get-param tau0_sq 1.0)))
(= (get-sigma-sq) (max 0.000001 (get-param sigma_sq 1.0)))
(= (get-kappa) (max 0.000001 (get-param kappa 1000.0)))
(= (get-global-weight) (max 0.000001 (get-param global_weight 1.0)))

;;; --------------------------------------------------------------------------
;;; Scoring
;;; --------------------------------------------------------------------------

(= (axiom-evidence $x $n)
   (xiPLN.cont.Evidence $n (* $n $x) (* $n (* $x $x))))

(= (lookup-normal-obs $axiom)
   (lookup_normal_obs_db $axiom))

(= (normal-score $axiom)
   (let* (($pair (lookup-normal-obs $axiom))
          ($mu0 (get-mu0))
          ($tau0sq (get-tau0-sq))
          ($sigmaSq (get-sigma-sq))
          ($kappa (get-kappa))
          ($gw (get-global-weight)))
     (if (== $pair ())
         (stv 0.5 0.0)
         (let ($x $nRaw) $pair
           (let* (($n (max 0.000001 (* $nRaw $gw)))
                  ($ev (axiom-evidence $x $n))
                  ($ctx (xiPLN.cont.Context $mu0 $tau0sq $sigmaSq)))
                 (xiPLN.cont.toProbSTV $ev $ctx $kappa))))))

;;; --------------------------------------------------------------------------
;;; Batched query execution
;;; --------------------------------------------------------------------------

(= (process-one-query $jobId ($qid $axiom))
   (let* (($stv (once (normal-score $axiom)))
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
     (let* (($_ (load_normal_db $dataFile))
            ($queryRows (parse_normal_queries_file $queryFile)))
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
         (println! "Usage: ./run.sh demos/pln_normal_nb_selector_jobs.metta <jobs.tsv>")
         (let* (($jobs (zar_jobs_parse_jobs_file $jobsFile)))
           (process-jobs $jobs)))))

!(once (main))
