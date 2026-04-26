; Translated from PeTTa to HE (9 atoms)
; Source: /home/zar/claude/tmp/petta-he-profile/examples/patrick_test.metta

!(import! &self (library lib_patrick))
(= (mirror (@ $L (cons $head $tail))) (append (reverse $L) $tail))
!(assertPeTTaTest (mirror (h a n n e s)) (s e n n a h a n n e s))
!(assertPeTTaTest (collapse (for $x (1 2 3 4 5 6) (if (> $x 3) $x))) (4 5 6))
!(assertPeTTaTest (iterate 0 10 1 (|-> ($i $x) (+ $x $i))) 46)
