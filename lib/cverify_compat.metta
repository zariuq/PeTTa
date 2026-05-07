!(import! &self system)
!(import! &self cverify_textual_parse)

(= (parse_mm_file $filename)
   (function
     (let $resolved (resolve-input-path $filename)
       (case (parse-metamath-file $resolved () ())
         (((ParsedStmts $stmts $seen) (return $stmts))
          (parse-unsupported (return parse-unsupported))
          ((Error $info $message)
           (return (Error (parse_mm_file $filename) $message))))))))

(= (get_cmdline_args)
   (function
     (case (system-args)
       (($result (return $result))))))

(= (get_cmdline_arg $idx)
   (function
     (case (system-arg $idx)
       (($result (return $result))))))

(= (cmdline_arg_count)
   (function
     (case (system-argc)
       (($result (return $result))))))

(= (has_cmdline_args)
   (function
     (case (system-has-args)
       (($result (return $result))))))

(= (get_env_var_or_default $name $default)
   (function
     (case (system-getenv-or-default $name $default)
       (($result (return $result))))))

(= (halt_with_code $code)
   (function
     (case (system-exit $code)
       (($result (return $result))))))

(= (is_flag_arg $arg)
   (function
     (case (system-flag-arg? $arg)
       ((True (return true))
        (False (return false))))))

(= (concat $a $b)
   (function
     (case (format-args "{}{}" ($a $b))
       (($result (return $result))))))
