!(import_prolog_function consult)
;consult/1 as a function has no inputs and the file as its output, so binding
;the output to the file loads it:
!(let $file (library lib_det.pl) (let $file (consult) loaded))
!(import_prolog_function det-verdict)
