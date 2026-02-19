;;; pln_normal_nb_selector.metta - Normal-Normal PLN premise selector
;;;
;;; This selector uses the PLN continuous evidence library:
;;;   Evidence: cont-ev(n, sum, sumSq)
;;;   Context:  cont-ctx(mu0, tau0_sq, sigma_sq)
;;;   Scoring:  xiPLN.cont.toProbSTV(evidence, context, kappa)
;;;
;;; Each axiom receives a continuous observation x (z-normalized NB score)
;;; with pseudo-count n. We then compute:
;;;   (stv strength confidence) = xiPLN.cont.toProbSTV(evidence, context, kappa)
;;;
;;; Usage:
;;;   ./run.sh demos/pln_normal_nb_selector.metta <data.tsv> <queries.tsv>
;;;
;;; Data TSV format:
;;;   param<TAB>mu0<TAB>value
;;;   param<TAB>tau0_sq<TAB>value
;;;   param<TAB>sigma_sq<TAB>value
;;;   param<TAB>kappa<TAB>value
;;;   param<TAB>global_weight<TAB>value
;;;   obs<TAB>axiom<TAB>x<TAB>n

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

(= (score-one-query ($qid $axiom))
   (Result $qid $axiom (once (normal-score $axiom))))

(= (score-all-queries $acc $qrows)
   (if (== (size-atom $qrows) 0)
       $acc
       (let ($q $rest) (decons-atom $qrows)
         (score-all-queries
           (TupleConcat $acc ((score-one-query $q)))
           $rest))))

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
           (println! "Usage: ./run.sh demos/pln_normal_nb_selector.metta <data.tsv> <queries.tsv>")
           (let* (($_ (load_normal_db $dataFile))
                  ($queryRows (parse_normal_queries_file $queryFile))
                  ($results (score-all-queries () $queryRows)))
             (print-results $results))))))

!(once (main))
