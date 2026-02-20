;Prolog interop: predicate-style consult/use_module wrappers
(: consult_file (-> Atom Atom))
(= (consult_file $prologfile)
   (callPredicate (Predicate (quote (consult $prologfile)))))

(: use_module_file (-> Atom Atom))
(= (use_module_file $prologfile)
   (callPredicate (Predicate (quote (use_module $prologfile)))))

;Import Prolog functions from a file (predicate-style, no main.pl wrappers needed)
(: import_prolog_functions_from_file_pred (-> Atom Expression Atom))
(= (import_prolog_functions_from_file_pred $prologfile $importfunctions)
   (let* (($ok (consult_file $prologfile))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

(: import_prolog_functions_from_module_pred (-> Atom Expression Atom))
(= (import_prolog_functions_from_module_pred $prologfile $importfunctions)
   (let* (($ok (use_module_file $prologfile))
          ($function (superpose $importfunctions)))
         (import_prolog_function $function)))

; Load Prolog helpers from lib_zar.pl (cmdline args, new-space, delete-space)
!(import_prolog_functions_from_file_pred "lib/lib_zar.pl"
  (get_cmdline_arg get_cmdline_args cmdline_arg_count has_cmdline_args new-space delete-space))
