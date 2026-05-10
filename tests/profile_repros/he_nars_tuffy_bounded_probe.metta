; Tiny HE witness for the NARS.Query path with explicit bounds.
; This is for profiling/runtime characterization, not full nars_tuffy parity.

!(import! &self ../../lib/lib_nars.metta)

; Silence derivation trace noise during profiling.
(= (println! $x) True)

(= (kb)
   ((Sentence ((==> (--> $1 ([] smokes))
                    (--> $1 ([] cancerous)))
               (stv 0.6 0.9)) (2))
    (Sentence ((--> Edward ([] smokes))
               (stv 1.0 0.9)) (10))))

!(let $_ (NARS.Query (kb)
                     (--> Edward ([] cancerous))
                     1
                     3
                     3)
      done)
