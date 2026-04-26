; Reduced HE repro for PLN.Query runtime blowup.
; Uses a smaller step horizon, repeated enough times to amplify the query path
; without letting one call take over the whole run.

!(import! &self ../../lib/lib_pln.metta)

; Silence derivation trace noise during profiling.
(= (println! $x) True)

(= (STV A) (stv 0.5 0.9))
(= (STV B) (stv 0.25 0.9))
(= (STV C) (stv 0.25 0.9))
(= (STV D) (stv 0.5 0.9))

(= (kb)
   ((Sentence ((Inheritance A B) (stv 0.25 0.9)) (1))
    (Sentence ((Inheritance A C) (stv 0.25 0.9)) (2))
    (Sentence ((Inheritance B D) (stv 0.5 0.9)) (3))
    (Sentence ((Inheritance C D) (stv 0.5 0.9)) (4))))

(= (repeat-pln 0) done)
(= (repeat-pln $n)
   (let $_ (PLN.Query (kb) (Inheritance A D) 4 30 100)
        (repeat-pln (- $n 1))))

!(repeat-pln 12)
