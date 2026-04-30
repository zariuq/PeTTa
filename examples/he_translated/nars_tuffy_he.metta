; Translated from PeTTa to HE (5 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/nars_tuffy.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self ../../lib/lib_nars.metta)
(= (kb) ((Sentence ((==> (--> (× $1 $2) friend) (==> (--> $1 ([] smokes)) (--> $2 ([] smokes)))) (stv 0.4 0.9)) (1)) (Sentence ((==> (--> $1 ([] smokes)) (--> $1 ([] cancerous))) (stv 0.6 0.9)) (2)) (Sentence ((--> (× Anna Bob) friend) (stv 1.0 0.9)) (3)) (Sentence ((--> (× Anna Edward) friend) (stv 1.0 0.9)) (4)) (Sentence ((--> (× Anna Frank) friend) (stv 1.0 0.9)) (5)) (Sentence ((--> (× Edward Frank) friend) (stv 1.0 0.9)) (6)) (Sentence ((--> (× Gary Helen) friend) (stv 1.0 0.9)) (7)) (Sentence ((--> (× Gary Frank) friend) (stv 0.0 0.9)) (8)) (Sentence ((--> Anna ([] smokes)) (stv 1.0 0.9)) (9)) (Sentence ((--> Edward ([] smokes)) (stv 1.0 0.9)) (10))))
!(assertPeTTaTest (NARS.Query (kb) (--> Edward ([] cancerous))) ((stv 0.6 0.48941156079382964) (2 5 6 9 10)))
