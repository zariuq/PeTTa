(= (scale-addK $K)
   (if (== $K 0)
       done
       (let* (($K10 (% $K 10))
              ($t (add-atom &self (rtest $K $K10))))
             (scale-addK (- $K 1)))))

(= (scale-q-all)
   (collapse (match &self (rtest $x $y) (rtest $x $y))))

(= (scale-q-first $a)
   (collapse (match &self (rtest $a $y) (rtest $a $y))))

(= (scale-q-second $b)
   (collapse (match &self (rtest $x $b) (rtest $x $b))))

(= (scale-q-both $a $b)
   (collapse (match &self (rtest $a $b) (rtest $a $b))))

(= (scale-q-rel $r)
   (collapse (match &self ($r 643 3) ($r 643 3))))

(= (scale-indexing-demo $K)
   (let* (($temp (scale-addK $K))
          ($all (scale-q-all))
          ($first (scale-q-first 7))
          ($second (scale-q-second 3))
          ($rel (scale-q-rel rtest))
          ($both (scale-q-both 42 2)))
         (all: (length $all) first: (length $first) second: (length $second) rel: (length $rel) both: (length $both))))

!(assertEqualToEval
  (scale-indexing-demo 1000)
  (all: 1000 first: 1 second: 100 rel: 1 both: 1))
