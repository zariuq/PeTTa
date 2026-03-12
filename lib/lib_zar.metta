;;; lib_zar.metta - shared MeTTa helper utilities for PeTTa demos

!(import! &self lib_import)
!(import_prolog_function consult)

; Prolog interop: predicate-style consult/use_module wrappers
(: consult_file (-> Atom Atom))
(= (consult_file $prologfile)
   (callPredicate (Predicate (quote (consult $prologfile)))))

(: use_module_file (-> Atom Atom))
(= (use_module_file $prologfile)
   (callPredicate (Predicate (quote (use_module $prologfile)))))

; Import Prolog functions from a file (predicate-style, no main.pl wrappers needed)
(: import_prolog_functions_from_file_pred (-> Atom Expression Atom))
(= (import_prolog_functions_from_file_pred $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

(: import_prolog_functions_from_module_pred (-> Atom Expression Atom))
(= (import_prolog_functions_from_module_pred $prologfile $importfunctions)
   (let* (($prologfile (use_module))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

;;; Back-compat helper: import Prolog predicates without exists_file checks.
;;; Useful when scripts run in environments where relative-path checks are noisy.
(= (import_prolog_functions_from_file_nocheck $prologfile $importfunctions)
   (let* (($prologfile (consult))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

; Shared lib_zar.pl helper surface: filtered cmdline access, space backends, profiling.
!(import_prolog_functions_from_file_pred "lib/lib_zar.pl"
  (get_cmdline get_cmdline_arg get_cmdline_args cmdline_arg_count has_cmdline_args
   new-space delete-space
   sp_new_map sp_new_map_fast sp_map_get sp_map_put sp_map_has sp_map_del
   sp_new_set sp_new_set_fast sp_set_add sp_set_has sp_set_del
   sp_set_union sp_set_subtract sp_set_from_list
   sp_delete sp_get_index sp_set_index
   ffi_counter_init ffi_counter_init_off ffi_counter_dump))

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
