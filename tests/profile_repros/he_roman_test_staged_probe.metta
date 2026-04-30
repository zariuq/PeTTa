; Staged debug repro for the translated roman_test timeout.

!(import! &self ../../lib/lib_roman.metta)

!(println! "DEBUG: roman-map-fold")
!(assertPeTTaTest (map-flat (+ 1) (1 2 3)) (2 3 4))
!(assertPeTTaTest (map-nested (+ 1) (1 (2 3))) (2 (3 4)))
!(assertPeTTaTest (fold-flat + 0 (1 2 3)) 6)
!(assertPeTTaTest (foldr-flat cons () (1 (2 3) 4)) (1 (2 3) 4))
!(assertPeTTaTest (fold-nested + 0 (1 (2 3))) 6)

!(println! "DEBUG: roman-set-ops")
!(assertPeTTaTest (/=\ (1 2 $a) (2 3 4)) (2 2))
!(assertPeTTaTest (/==\ (1 2 3) (2 3 4)) (2 3))
!(assertPeTTaTest (/=a\ (1 2 $a) (2 $a 4)) (2 $a))
!(assertPeTTaTest (\= (1 2 3) ($a 3 4)) (2))
!(assertPeTTaTest (\== (1 2 3) (2 3 4)) (1))
!(assertPeTTaTest (\=a (1 2 $a) (2 $a 4)) (1))
!(assertPeTTaTest (\=/ (1 2 3) ($a 3 4)) (2 1 3 4))
!(assertPeTTaTest (\==/ (1 2 3) (2 3 4)) (1 2 3 4))
!(assertPeTTaTest (\=a/ (1 2 $a) (2 $a 4)) (1 2 $a 4))

!(println! "DEBUG: roman-composition")
!(assertPeTTaTest (. (+ 1) (* 2) 1) 3)
!(assertPeTTaTest (.: (+ 1) + 2 3) 6)
!(assertPeTTaTest (&&& (+ 2) (* 2) 1) (3 2))

(= (mfail $x) (empty))
!(assertPeTTaTest (collapse (&^& (+ 1) (mfail) 1)) (2))

!(println! "DEBUG: roman-patterns")
!(assertPeTTaTest (let (@ $lst (cons $h $t)) (1 2 3) ($lst $h $t)) ((1 2 3) 1 (2 3)))
!(assertPeTTaTest (let (head $x) (1 2 3) $x) 1)
!(assertPeTTaTest (let (tail $xs) (1 2 3) $xs) (2 3))
!(assertPeTTaTest (let (mylast $x) (1 2 3) $x) 3)
!(assertPeTTaTest (let (init $xs) (1 2 3) $xs) (1 2))
!(assertPeTTaTest (let (rcons $xs $x) (1 2 3) ($xs $x)) ((1 2) 3))

!(println! "DEBUG: roman-prog")
!(assertPeTTaTest (let $__tr_result_1 (+ 1 1) (chain (+ 2 2) $__tr_discard_2 $__tr_result_1)) 2)
!(assertPeTTaTest (chain (+ 1 1) $__tr_discard_3 (+ 2 2)) 4)
