; PeTTa --he should preserve ordinary PeTTa function-head patterns for
; translated examples and libraries.

(= (head-len ()) 0)
(= (head-len (cons $head $tail))
   (+ 1 (head-len $tail)))

!(assertEqual (head-len (a b c)) 3)

(= (head-append $xs $ys)
   (append (append (42) $xs) $ys))

(= (head-rel (head-append (10) $rest) $tag)
   ($rest $tag))

!(assertEqual
  (head-rel (42 10 40) ok)
  ((40) ok))
