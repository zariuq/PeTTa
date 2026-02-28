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

; Load Prolog helpers from lib_zar.pl (cmdline args, new-space, delete-space, MapSpace, SetSpace)
!(import_prolog_functions_from_file_pred "lib/lib_zar.pl"
  (get_cmdline_arg get_cmdline_args cmdline_arg_count has_cmdline_args new-space delete-space
   sp_new_map sp_new_map_fast sp_map_get sp_map_put sp_map_has sp_map_del
   sp_new_set sp_new_set_fast sp_set_add sp_set_has sp_set_del
   sp_set_union sp_set_subtract sp_set_from_list
   sp_delete sp_get_index sp_set_index
   ffi_counter_init ffi_counter_init_off ffi_counter_dump))
