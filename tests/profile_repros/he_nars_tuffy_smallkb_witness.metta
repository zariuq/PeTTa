; Reduced HE witness for the nars_tuffy query path.
; This keeps the imported lib_nars + Sentence-space + NARS.Query surface, but
; shrinks the knowledge base to a single direct smokes=>cancerous inference.

!(import! &self ../../lib/lib_nars.metta)

(= (kb)
   ((Sentence ((==> (--> $1 ([] smokes))
                    (--> $1 ([] cancerous)))
               (stv 0.6 0.9)) (2))
    (Sentence ((--> Edward ([] smokes))
               (stv 1.0 0.9)) (10))))

!(test
  (NARS.Query (kb)
              (--> Edward ([] cancerous)))
  ((stv 0.6 0.486) (2 10)))
