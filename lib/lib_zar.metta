;;; lib_zar.metta - shared MeTTa helper utilities for PeTTa demos

!(import! &self lib_import)
!(import_prolog_function consult)

;;; Import Prolog predicates without exists_file checks.
;;; Useful when scripts run in environments where relative-path checks are noisy.
(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

;;; CLI helper: true when argument begins with "--"
(= (starts-with-dash $str)
   (case $str
     (("--" True)
      ($_ False))))

;;; First non-flag command-line argument from index.
(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         (let $is_flag (starts-with-dash $arg)
           (if (== $is_flag True)
               (get-first-non-flag-arg (+ $idx 1))
               $arg)))))
