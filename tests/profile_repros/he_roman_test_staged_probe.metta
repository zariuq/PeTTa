; Staged debug repro for the translated roman_test timeout.

!(import! &self ../../lib/lib_roman.metta)

!(println! "DEBUG: roman-map-fold")
!(assertEqualToEval (map-flat (+ 1) (1 2 3)) (2 3 4))
!(assertEqualToEval (map-nested (+ 1) (1 (2 3))) (2 (3 4)))
!(assertEqualToEval (fold-flat + 0 (1 2 3)) 6)
!(assertEqualToEval (foldr-flat cons () (1 (2 3) 4)) (1 (2 3) 4))
!(assertEqualToEval (fold-nested + 0 (1 (2 3))) 6)

!(println! "DEBUG: roman-set-ops")
!(assertEqualToEval (/=\ (1 2 $a) (2 3 4)) (2 2))
!(assertEqualToEval (/==\ (1 2 3) (2 3 4)) (2 3))
!(assertEqualToEval (/=a\ (1 2 $a) (2 $a 4)) (2 $a))
!(assertEqualToEval (\= (1 2 3) ($a 3 4)) (2))
!(assertEqualToEval (\== (1 2 3) (2 3 4)) (1))
!(assertEqualToEval (\=a (1 2 $a) (2 $a 4)) (1))
!(assertEqualToEval (\=/ (1 2 3) ($a 3 4)) (2 1 3 4))
!(assertEqualToEval (\==/ (1 2 3) (2 3 4)) (1 2 3 4))
!(assertEqualToEval (\=a/ (1 2 $a) (2 $a 4)) (1 2 $a 4))

!(println! "DEBUG: roman-composition")
!(assertEqualToEval (. (+ 1) (* 2) 1) 3)
!(assertEqualToEval (.: (+ 1) + 2 3) 6)
!(assertEqualToEval (&&& (+ 2) (* 2) 1) (3 2))

(= (mfail $x) (empty))
!(assertEqualToEval (collapse (&^& (+ 1) (mfail) 1)) (2))

!(println! "DEBUG: roman-patterns")
!(assertEqualToEval (let (@ $lst (cons $h $t)) (1 2 3) ($lst $h $t)) ((1 2 3) 1 (2 3)))
!(assertEqualToEval (let (head $x) (1 2 3) $x) 1)
!(assertEqualToEval (let (tail $xs) (1 2 3) $xs) (2 3))
!(assertEqualToEval (let (mylast $x) (1 2 3) $x) 3)
!(assertEqualToEval (let (init $xs) (1 2 3) $xs) (1 2))
!(assertEqualToEval (let (rcons $xs $x) (1 2 3) ($xs $x)) ((1 2) 3))

!(println! "DEBUG: roman-prog")
!(assertEqualToEval (let $__tr_result_1 (+ 1 1) (chain (+ 2 2) $__tr_discard_2 $__tr_result_1)) 2)
!(assertEqualToEval (chain (+ 1 1) $__tr_discard_3 (+ 2 2)) 4)
