; Reduced HE repro for NARS.Query runtime explosion.
; Uses the smallest horizon that still exercises the query path, repeated to
; amplify runtime cost while staying finite.

!(import! &self ../../lib/lib_nars.metta)

; Silence derivation trace noise during profiling.
(= (println! $x) True)

(= (kb)
   ((Sentence ((==> (--> (× $1 $2) friend)
                    (==> (--> $1 ([] smokes))
                         (--> $2 ([] smokes))))
               (stv 0.4 0.9)) (1))
    (Sentence ((==> (--> $1 ([] smokes))
                    (--> $1 ([] cancerous)))
               (stv 0.6 0.9)) (2))
    (Sentence ((--> (× Anna Bob) friend)
               (stv 1.0 0.9)) (3))
    (Sentence ((--> (× Anna Edward) friend)
               (stv 1.0 0.9)) (4))
    (Sentence ((--> (× Anna Frank) friend)
               (stv 1.0 0.9)) (5))
    (Sentence ((--> (× Edward Frank) friend)
               (stv 1.0 0.9)) (6))
    (Sentence ((--> (× Gary Helen) friend)
               (stv 1.0 0.9)) (7))
    (Sentence ((--> (× Gary Frank) friend)
               (stv 0.0 0.9)) (8))
    (Sentence ((--> Anna ([] smokes))
               (stv 1.0 0.9)) (9))
    (Sentence ((--> Edward ([] smokes))
               (stv 1.0 0.9)) (10))))

(= (repeat-nars 0) done)
(= (repeat-nars $n)
   (let $_ (NARS.Query (kb) (--> Edward ([] cancerous)) 1 10 100)
        (repeat-nars (- $n 1))))

!(repeat-nars 20)
