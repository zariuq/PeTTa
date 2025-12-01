!(import_prolog_function consult)

(= (import_prolog_functions_from_file $prologfile $importfunctions) (let* (($prologfile (consult))
                                                                           ($function (superpose $importfunctions)))
                                                                          (import_prolog_function $function)))

!(import_prolog_function use_module)

(= (import_prolog_functions_from_module $prologfile $importfunctions) (let* (($prologfile (use_module))
                                                                             ($function (superpose $importfunctions)))
                                                                            (import_prolog_function $function)))

!(import_prolog_functions_from_file ./lib/lib_prolog (static-import!))

;;; Command-line argument access
;;; These functions are defined in src/main.pl and provide access to command-line arguments
;;; passed after the script filename.
;;;
;;; Usage:
;;;   ./run.sh script.metta arg1 arg2 arg3
;;;
;;; In script.metta:
;;;   !(import! &self lib_prolog)
;;;   !(let $file (get_cmdline_arg 0) ...)  ; Get first arg
;;;   !(let $count (cmdline_arg_count) ...) ; Get arg count
;;;   !(let $all (get_cmdline_args) ...)    ; Get all args as list

!(import_prolog_function get_cmdline_arg)
!(import_prolog_function get_cmdline_args)
!(import_prolog_function cmdline_arg_count)
!(import_prolog_function has_cmdline_args)

;; Note: get_cmdline_arg returns atoms from Prolog, not typed strings
;; Using Atom type instead of String to match Prolog atom return
(: get_cmdline_arg (-> Number Atom))
(: get_cmdline_args (-> Expression))
(: cmdline_arg_count (-> Number))
(: has_cmdline_args (-> Bool))
